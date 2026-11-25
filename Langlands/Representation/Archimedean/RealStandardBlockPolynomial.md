# The block polynomial of a real standard module

Module `Langlands.Representation.Archimedean.RealStandardBlockPolynomial`.
Helper module of the proof that real standard modules are nonzero
(`Langlands.Archimedean.realStandardNontrivial`, module
`Langlands.Representation.Archimedean.RealStandardNontrivialProof`), used in the proof of
`CuspidalArchimedeanStandardGenericStatement`.

For a list `ds` of real blocks, the module defines a polynomial `blockPoly n ds 0` in the entries
`X_ij` of an `n × n` matrix. Its Gram function (module `RealGramFunction`) is the nonzero vector of
the real standard module `realStandardModule n ds`. This module proves the algebraic facts used:
the value at the identity, the sign parity, the factorization at an induction block, and how the
factor of a block behaves under a rotation of its two rows.

Notation: `RealBlock`, `RealCharacterData`, `ComplexCharacterData`, `realRank`,
`realInducedBlockAt`, `realInducedFirstCharacter` and `realInducedSecondCharacter` are the
Library's (`Langlands.LocalFactor.Archimedean` and the module `StandardModule`).
`realPositionCharacter`, `realPositionExponent`, `signReal` and `signUnit` come from the Library
module `PrincipalSeriesGramFormula`. `ia h, ib h : Fin n` are the indices `p, p + 1` for
`h : p + 1 < n` (Library module `RealBlockRotation`). `HasSignParity` is defined in
`RealGramFunction`. Declarations below are in the namespace
`Langlands.Archimedean.RealStandardNontrivial`.

## Definitions

* `var n i j`: the variable `X_ij` at natural-number indices, and `0` if `i` or `j` is `≥ n`.
* `lplus n q = X_qq + X_{q+1,q+1} + i (X_{q,q+1} - X_{q+1,q})` and
  `lminus n q = X_{q+1,q+1} - X_qq - i (X_{q,q+1} + X_{q+1,q})`.
* `blockFactor n q N = Φ_q = lplus^N + (-1)^N lminus^N`.
* `blockPoly n ds q`, by recursion on `ds` (first position `q`):
  * `blockPoly n [] q = 1`;
  * a character block `d` contributes `X_qq^(d.parity)` and continues at `q + 1`;
  * an induction block `d` contributes `Φ_q` with `N = |d.weight| + 1` and continues at `q + 2`.
* `oneEntries n`: the entries of the identity matrix, as complex numbers.
* `unitAt a i`: `a_i` for `i < n`, else `1`. `signedEntries a Y`: row `i` of `Y` multiplied by
  `signReal a_i`.
* `DependsOnRows S R`: the value of `R` depends only on the rows with index in `S`.
* `IsRowRotation h u v Y Y'`: `Y'` is `Y` with rows `p, p + 1` replaced by `u Y_p - v Y_{p+1}` and
  `v Y_p + u Y_{p+1}`, other rows unchanged.

## Main theorems

```lean
theorem eval_one_blockPoly_ne_zero : ∀ (ds : List RealBlock) (q : ℕ), q + realRank ds ≤ n →
    MvPolynomial.eval (oneEntries n) (blockPoly n ds q) ≠ 0

theorem hasSignParity_blockPoly (ds : List RealBlock) (hds : realRank ds = n) :
    HasSignParity (realPositionCharacter ds) (blockPoly n ds 0)

theorem exists_blockPoly_eq_blockFactor_mul : ∀ (ds : List RealBlock) (q p : ℕ)
    (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
    ∃ R : MvPolynomial (Fin n × Fin n) ℂ,
      blockPoly n ds q = blockFactor n (q + p) (d.weight.natAbs + 1) * R ∧
        DependsOnRows {l | l ≠ q + p ∧ l ≠ q + p + 1} R

theorem eval_rotated_blockFactor_mul {p : ℕ} (h : p + 1 < n) (N : ℕ)
    {R : MvPolynomial (Fin n × Fin n) ℂ} (hR : DependsOnRows {l | l ≠ p ∧ l ≠ p + 1} R)
    {u v : ℂ} {Y Y' : Fin n × Fin n → ℂ} (hY : IsRowRotation h u v Y Y') :
    MvPolynomial.eval Y' (blockFactor n p N * R) =
      ((u - Complex.I * v) ^ N * MvPolynomial.eval Y (lplus n p) ^ N +
        (-1 : ℂ) ^ N * (u + Complex.I * v) ^ N * MvPolynomial.eval Y (lminus n p) ^ N) *
        MvPolynomial.eval Y R

theorem realPositionExponent_of_blockAt : ∀ {ds : List RealBlock} {p : ℕ}
    {d : ComplexCharacterData}, realInducedBlockAt ds p = some d →
    realPositionExponent ds p - realPositionExponent ds (p + 1) = (d.weight.natAbs : ℂ)
```

## Proofs

* **Value at the identity** (`eval_one_blockPoly_ne_zero`, induction on `ds`). At the identity,
  `X_qq = 1`, `lplus = 2` and `lminus = 0`, so `Φ_q(1) = 2^N` with `N ≥ 1`
  (`eval_blockFactor_one`), and each character factor is `1`.
* **Sign parity** (`eval_signed_blockPoly`, induction on `ds`). A character block of parity `ε` at
  `q` contributes `signReal(a_q)^ε`. That is the value of its character at `signUnit a_q`
  (`character_signUnit`). For an induction block, there are four sign cases for `(a_p, a_{p+1})`.
  Changing the sign of a row exchanges `lplus` and `±lminus`, and in each case
  `Φ_p ↦ signReal(a_p)^N Φ_p` (`eval_signed_blockFactor`). This matches the characters
  `realInducedFirstCharacter d (signUnit x) = signReal(x)^N` and
  `realInducedSecondCharacter d (signUnit x) = 1`. `hasSignParity_blockPoly` is the case `q = 0`,
  `realRank ds = n`.
* **Factorization** (`exists_blockPoly_eq_blockFactor_mul`, induction on `ds` and the position).
  The cofactor `R` is the product of the factors of the other blocks. Their variables lie in other
  rows (`dependsOnRows_var`, `dependsOnRows_blockFactor`, `dependsOnRows_blockPoly` and closure
  under `+`, `-`, `·`, powers).
* **Rotation** (`eval_lplus_rotation`, `eval_lminus_rotation`). Under the row rotation, `lplus`
  is multiplied by `u - iv` and `lminus` by `u + iv` (a `linear_combination` with `i² = -1`). The
  cofactor `R` is unchanged because it is free of these rows.
* **Exponents** (`realPositionExponent_of_blockAt`). The Library exponents of an induction block
  are `d.exponent ± |d.weight|/2`.

## Provenance

The construction is internal to the project. For `GL_2(ℝ)` and `M = [[a, b], [c, d]]` with the
rotation acting on rows, `Φ` is a polynomial in the rows of `M`. After the Gram–Schmidt
normalization in `RealGramFunction`, the Gram function of `Φ` is a combination of
`(d' ∓ i c')^(-N)`-type functions (module `RealStandardNontrivialProof`). That is the explicit
lowest-weight vector of the induced representation of weight `N`. No literature source is claimed
for these lemmas.

## Lean checks

The module was checked alone and built together with the other nonvanishing modules. No errors or
warnings. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.
