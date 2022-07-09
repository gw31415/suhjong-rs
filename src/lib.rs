#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn detect_errors() {
        use ErrorCode::*;
        assert_eq!(check(*b"2+2=5+0+0").unwrap_err(), ValueMismatch);
        assert_eq!(check(*b"2/0=2/0+0").unwrap_err(), Math);
        assert_eq!(check(*b"1-2+1=0+0").unwrap_err(), Overflow);
        assert_eq!(check(*b"256=1+0").unwrap_err(), Overflow);
        assert_eq!(check(*b"99*3=41").unwrap_err(), Overflow);
        assert_eq!(check(*b"-7+7=5-2-3").unwrap_err(), Parse);
        assert_eq!(check(*b"0+-0=0+0+0").unwrap_err(), Parse);
        assert_eq!(check(*b"1+2-3=0+0=0").unwrap_err(), MultipleEquals);
        assert_eq!(check(*b"0+0+2+2-4").unwrap_err(), NoEquals);
        assert_eq!(check(*b"1a2=12+3").unwrap_err(), UndefinedCharacter);
        assert_eq!(check(*b"12+3=10+5").unwrap_err(), NumCountAgainstRules);
        assert_eq!(check(*b"1+2+3-4=2").unwrap_err(), NumCountAgainstRules);
        assert_eq!(check(*b"01=2-1+0").unwrap_err(), HighestRankZero);
    }
}

#[derive(Debug, PartialEq, Eq)]
#[repr(u8)]
/// このライブラリにおけるエラーコードを表します。
/// 値の型は`u8`です。
pub enum ErrorCode {
    /// The numbers on both sides do not match.
    ValueMismatch = 0,
    /// A mathematical error occurred.
    Math = 1,
    /// Overflow occurred.
    Overflow = 2,
    /// Syntax Error.
    Parse = 3,
    /// Multiple equal signs found.
    MultipleEquals = 4,
    /// No equal sign found.
    NoEquals = 5,
    /// Character not defined for operation.
    UndefinedCharacter = 6,
    /// Number of digits is against the rules.
    NumCountAgainstRules = 7,
    /// Zero is not allowed in the highest position of multi-digit number in rank notation.
    HighestRankZero = 8,
}

/// 文字の型
pub type Char = u8;

/// 数値の型
pub type Num = u8;

/// 位取り記数法の基数
pub const RADIX: Num = 10;

/// 等号を表す文字
pub const EQUAL_SIGN: Char = b'=';

/// 一人あたりの手札の枚数
pub const DIGITS_COUNT: usize = 5;

/// シンボルと2項間演算を紐付ける
fn operate(symbol: Char, a: Num, b: Num) -> Result<Num, ErrorCode> {
    use ErrorCode::*;
    if let Some(value) = match symbol {
        b'+' => a.checked_add(b),
        b'-' => a.checked_sub(b),
        b'*' => a.checked_mul(b),
        b'/' => {
            if b == 0 || a % b != 0 {
                return Err(Math);
            } else {
                Some(a / b)
            }
        }
        _ => {
            return Err(UndefinedCharacter);
        }
    } {
        Ok(value)
    } else {
        Err(ErrorCode::Overflow)
    }
}

/// シンボルと数字を紐付ける
fn num(char: Char) -> Option<Num> {
    if char >= b'0' && char <= b'9' {
        Some(char - b'0')
    } else {
        None
    }
}

mod calculation {
    use super::*;

    enum CalcState {
        FirstNumWaiting,
        FirstNumInput(Num),
        SecondNumWaiting {
            first: Num,
            operator: Char,
        },
        SecondNumInput {
            first: Num,
            second: Num,
            operator: Char,
        },
    }

    /// 四則演算を行う評価器。
    /// 入力文字列は左から順に評価される。
    /// 演算子の優先順位は考慮されず、括弧はなし。
    /// 計算は中置記法の演算子：`+-*/` 。
    /// 最高位に0は使えない。
    struct Calculator {
        state: CalcState,
        nums: Vec<Num>,
    }
    impl Calculator {
        /// 初期化済みCalculatorを返します。
        fn new() -> Self {
            Self {
                state: CalcState::FirstNumWaiting,
                nums: Default::default(),
            }
        }

        /// 1文字入力します。
        fn input(&mut self, char: Char) -> Result<(), ErrorCode> {
            use CalcState::*;
            if let Some(n) = num(char) {
                // 数字のとき
                self.nums.push(n);
                self.state = match &self.state {
                    FirstNumWaiting => FirstNumInput(n),
                    FirstNumInput(first) => {
                        // 数字入力の途中を表している。
                        // つまり数字の2文字目以降の数字が入力されたということ。
                        // この時点で入力途中の数の値が0ということは、
                        // 最高位が0で、今入力された文字が2桁目であることしかありえないため、
                        // エラー：`HighestRankZero`が返される。
                        if first == &0u8 {
                            return Err(ErrorCode::HighestRankZero);
                        }
                        FirstNumInput(
                            RADIX
                                .checked_mul(*first)
                                .ok_or(ErrorCode::Overflow)?
                                .checked_add(n)
                                .ok_or(ErrorCode::Overflow)?,
                        )
                    }
                    SecondNumWaiting { first, operator } => SecondNumInput {
                        first: *first,
                        second: n,
                        operator: *operator,
                    },
                    SecondNumInput {
                        first,
                        second,
                        operator,
                    } => {
                        // 数字入力の途中を表している。
                        // つまり数字の2文字目以降の数字が入力されたということ。
                        // この時点で入力途中の数の値が0ということは、
                        // 最高位が0で、今入力された文字が2桁目であることしかありえないため、
                        // エラー：`HighestRankZero`が返される。
                        if first == &0u8 {
                            return Err(ErrorCode::HighestRankZero);
                        }
                        SecondNumInput {
                            first: *first,
                            second: second * RADIX + n,
                            operator: *operator,
                        }
                    }
                };
                Ok(())
            } else {
                self.state = match &self.state {
                    FirstNumInput(first) => SecondNumWaiting {
                        first: *first,
                        operator: char,
                    },
                    SecondNumInput {
                        operator,
                        first,
                        second,
                    } => SecondNumWaiting {
                        first: operate(*operator, *first, *second)?,
                        operator: char,
                    },
                    _ => {
                        return Err(ErrorCode::Parse);
                    }
                };
                Ok(())
            }
        }

        /// 入力済みの式に従って計算結果を返します。
        fn calc(&mut self) -> Result<Num, ErrorCode> {
            use CalcState::*;
            let res = match self.state {
                FirstNumInput(n) => Ok(n),
                SecondNumInput {
                    first,
                    second,
                    operator,
                } => Ok(operate(operator, first, second)?),
                _ => Err(ErrorCode::Parse),
            };
            self.state = FirstNumWaiting;
            res
        }
    }

    enum CheckState {
        /// 左辺を入力中
        LeftSide(Calculator),
        /// 右辺を入力中
        RightSide { left: Calculator, right: Calculator },
    }

    /// 数雀文字列を評価します。
    /// # Examples
    /// ```
    /// use suhjong::{check, ErrorCode};
    ///
    /// assert_eq!(check(*b"9+3=8/2+8").unwrap(), 12);
    /// // 演算の優先順位は左からになります。
    /// assert_eq!(check(*b"2+2*5=20").unwrap(), 20);
    /// assert_eq!(check(*b"2+2=5+0+0").unwrap_err(), ErrorCode::ValueMismatch);
    /// ```
    pub fn check(equation: impl IntoIterator<Item = Char>) -> Result<Num, ErrorCode> {
        let mut state = CheckState::LeftSide(Calculator::new());
        let mut equation = equation.into_iter();
        while let Some(char) = equation.next() {
            if char == EQUAL_SIGN {
                state = match state {
                    CheckState::RightSide { .. } => {
                        return Err(ErrorCode::MultipleEquals);
                    }
                    CheckState::LeftSide(calc) => CheckState::RightSide {
                        left: calc,
                        right: Calculator::new(),
                    },
                };
            } else {
                state = match state {
                    CheckState::LeftSide(mut left) => {
                        left.input(char)?;
                        CheckState::LeftSide(left)
                    }
                    CheckState::RightSide { mut right, left } => {
                        right.input(char)?;
                        CheckState::RightSide { left, right }
                    }
                }
            }
        }
        match state {
            CheckState::LeftSide(_) => Err(ErrorCode::NoEquals),
            CheckState::RightSide {
                mut left,
                mut right,
            } => {
                if left.nums.len() + right.nums.len() != DIGITS_COUNT
                    || left.nums.len() > 3
                    || left.nums.len() < 2
                {
                    return Err(ErrorCode::NumCountAgainstRules);
                }
                let (l, r) = (left.calc()?, right.calc()?);
                if l == r {
                    Ok(l)
                } else {
                    Err(ErrorCode::ValueMismatch)
                }
            }
        }
    }
}
pub use calculation::check;

use std::collections::HashSet;

/// 与えられた手札で得られる最大のスコアを計算します。
/// 第一返値はスコア、第二返値はそのスコアを実現する等式の文字列の`Vec`となっています。
///
/// # WARNING
/// 入力はASCIIコードにおける数字5つ( `^\d{5}$` )であり、
/// `u8`の数値ではない。
/// 引数のチェックはされないので注意すること。
///
/// # Examples
/// ```
/// use suhjong::{Num, Char, maximum_score};
/// use std::collections::HashSet;
///
/// let (score, eqns): (Num, HashSet<String>) = maximum_score(*b"98765");
/// assert_eq!(96, score);
/// ```
///
/// # TODO
/// * `cards`に同じ`Char`が含まれている場合、探索時の順列内に一時的に重複したカードセットが作成されてしまうため、
///   これを改善する。
pub fn maximum_score(cards: [Char; DIGITS_COUNT]) -> (Num, HashSet<String>) {
    use itertools::Itertools;
    const OPERATIONS: &[u8; 5] = b"+-*/ ";

    let mut res: (Num, HashSet<String>) = (0u8, Default::default());
    for card_set in cards
        .into_iter()
        .permutations(DIGITS_COUNT)
        .collect::<HashSet<Vec<Char>>>()
    {
        let (a, b, c, x, y) = (
            card_set[0],
            card_set[1],
            card_set[2],
            card_set[3],
            card_set[4],
        );
        let leftsides: Vec<Vec<u8>> = vec![
            vec![a, b, b'+', c],
            vec![a, b, b'-', c],
            vec![a, b, b'*', c],
            vec![a, b, b'/', c],
            vec![a, b'+', b, b'+', c],
            vec![a, b'+', b, b'-', c],
            vec![a, b'+', b, b'*', c],
            vec![a, b'+', b, b'/', c],
            vec![a, b'-', b, b'+', c],
            vec![a, b'-', b, b'-', c],
            vec![a, b'-', b, b'*', c],
            vec![a, b'-', b, b'/', c],
            vec![a, b'*', b, b'+', c],
            vec![a, b'*', b, b'-', c],
            vec![a, b'*', b, b'*', c],
            vec![a, b'*', b, b'/', c],
            vec![a, b'/', b, b'+', c],
            vec![a, b'/', b, b'-', c],
            vec![a, b'/', b, b'*', c],
            vec![a, b'/', b, b'/', c],
        ];
        for mut leftside in leftsides {
            leftside.push(EQUAL_SIGN);
            let leftside = leftside;
            for o in OPERATIONS {
                let mut eqn = leftside.clone();
                eqn.push(x);
                if o != &b' ' {
                    eqn.push(*o);
                }
                eqn.push(y);
                if let Ok(num) = check(eqn.clone()) {
                    let eqn = unsafe { std::mem::transmute::<Vec<u8>, String>(eqn) };
                    res = {
                        let (num_before, eqns_before) = res;
                        if num > num_before {
                            (num, vec![eqn].into_iter().collect())
                        } else if num == num_before && num != 0 {
                            // `num`が0の時は実質無役であり、
                            // 成立する等式を返す必要がないため
                            // `eqn`に追加しない。
                            let mut eqns = eqns_before;
                            eqns.insert(eqn);
                            (num_before, eqns)
                        } else {
                            (num_before, eqns_before)
                        }
                    }
                }
            }
        }
    }
    res
}
