# Algebraic relations between primitive elements are additive

Worker 716. Internal step of the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. No
registered source was used. The argument below is the one implemented in Lean.

## Main result

`exists_additive_relation`: in a commutative bialgebra `B` over a field `k`,
let `y` and `t` be primitive elements satisfying a nonzero polynomial relation
`c₀(y, t) = 0` with `c₀ : k[X][X]`. Then there are additive polynomials `α, β`
(in the sense of `Additive`), not both zero, with `α(y) + β(t) = 0`.

## Coefficient bookkeeping

`coeff2 c a b` is the coefficient of `X^a Y^b` in `c`, with `X` inner and `Y`
outer. `ext2` is extensionality for it. `Bdd D c` says all exponents are at
most `D` (`exists_bdd`). `mk2 D h` is the polynomial with coefficients `h a b`
for `a, b ≤ D`. `Below n m g` says every nonzero coefficient `X^a Y^b` of `g`
has `(b, a) < (n, m)` in the lexicographic order. `exists_minimal` (two
applications of `Nat.find`) chooses a nonzero relation `c` that is minimal for
this order at its leading exponent `(n, m)`. Here `n` is the `Y`-degree and
`m` is the `X`-degree of the leading coefficient. Every relation `g` with
`Below n m g` is then zero.

## Taylor expansion

`ev2_add_add` is the two-variable Taylor formula

`c(u' + u, v' + v) = ∑_{i,j ≤ D} H_{ij}(u', v') uⁱ vʲ`.

Here `H_{ij} = taylorCoeff c i j` is the composite of Hasse derivatives in
both variables. It is proved from Mathlib's `taylor_eval` via
`eval_add_eq_sum`, `ev2_add_right` and `ev2_add_left`. By
`coeff2_taylorCoeff`, the coefficient of `X^a Y^b` in `H_{ij}` is
`choose (a+i) i · choose (b+j) j · coeff2 c (a+i) (b+j)`.

For primitive `y, t` the comultiplication is an algebra map sending `y` to
`y ⊗ 1 + 1 ⊗ y` and `t` to `t ⊗ 1 + 1 ⊗ t`. So `comul_ev2_eq_sum` gives

`Δ(c(y, t)) = ∑ (yⁱ tʲ) ⊗ H_{ij}(y, t)`.

Contracting the right factor with a functional `φ` (`ev2_contract`) gives a
new relation `h_φ(y, t) = 0`, where `h_φ = mk2 D (φ(H_{ij}(y, t)))`.

## Implemented argument

Fix a minimal relation `c` with leading exponent `(n, m)`.

1. By `coeff2_taylorCoeff`, the Taylor coefficients at or above the leading
   exponent are constants: `H_{ab} = coeff2 c a b`. This is lemma `htop` in
   the proof; it uses `taylorCoeff_eq_C_C` and `support_le`.
2. For every functional `φ`, the relation `h_φ - φ(1)·c` is `Below n m`,
   because its coefficient at and above `(n, m)` cancels by step 1. By
   minimality it vanishes. Hence `φ(H_{ij}(y, t)) = φ(1)·coeff2 c i j` for all
   `φ`. Since functionals separate points, `H_{ij}(y, t)` is the constant
   `coeff2 c i j`.
3. For `(i, j) ≠ (0, 0)`, the polynomial `H_{ij} - coeff2 c i j` is therefore a
   relation. Its coefficients are shifts of coefficients of `c` by a nonzero
   amount, so it is `Below n m`. By minimality, `H_{ij}` is a constant
   polynomial. Comparing coefficients gives
   `choose (a+i) i · choose (b+j) j · coeff2 c (a+i) (b+j) = 0` whenever
   `(i, j) ≠ 0` and `(a, b) ≠ 0`.
4. Applying the counit to `c(y, t) = 0` gives `coeff2 c 0 0 = 0`, since
   primitive elements have counit zero.
5. Taking `(i, j, a, b) = (a', 0, 0, b')` shows that all mixed coefficients
   vanish. So `c = α(X) + β(Y)` with `α = c.coeff 0` and
   `β = c.map constantCoeff`. The remaining cases of step 3, together with
   `isAdditive_of_coeff`, show that `α` and `β` are additive. They are not both
   zero because `c ≠ 0`, and `α(y) + β(t) = c(y, t) = 0`.
