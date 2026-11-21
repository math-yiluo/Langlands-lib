# Characters of the upper triangular Borel subgroup of `GL_n(ℂ)`

Module: `Langlands.Representation.Archimedean.ComplexJacquetBorel`.

## Purpose and provenance

This is the third helper module for `Langlands.Archimedean.complexJacquetFrobenius` (see
`ComplexJacquetFrobeniusProof.md`). The Frobenius function attached to a Jacquet functional has
the form `g = βκ ↦ χ(β) ℓ(ρ(κ) w)`, where `β` is upper triangular, `κ` is unitary and `χ` is a
character of the upper triangular Borel subgroup. This module defines that character on
matrices, proves its multiplicativity and smoothness, and identifies it with the character used
by the Library's principal series `principalSeries` (module `StandardModule`). It also constructs
the complex characters `characterOfParams l t` that make up the target standard module.

The formulas are elementary. The only conventions involved are the Library's: a
`ComplexCharacterData` (module `LocalFactor.ArchimedeanAttachment`) is a continuous character
`z ↦ (z/‖z‖)^{weight} ‖z‖^{2·exponent}` of `ℂˣ`, and `principalSeriesCharacter ℂ n χ a` is
`∏ᵢ χ_i(a_i) (‖a_i‖²)^{(n−1)/2 − i}`, which is the character of the normalized induction
(`δ^{1/2}` with `δ` the modulus character of the Borel subgroup). `borelFactor`, `borelChar` and
`characterOfParams` are auxiliary definitions of this formalization.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

### The factor `z ↦ (z/‖z‖)^l ‖z‖^α`

- `borelFactor l α z` (definition): `(z/‖z‖)^l · exp(α log ‖z‖)` for `l ∈ ℤ`, `α ∈ ℂ`, `z ∈ ℂ`.
- `borelFactor_eq_cpow`: for `z ≠ 0` it equals `(z/‖z‖)^l ‖z‖^α` with the complex power.
- `borelFactor_ne_zero`, `borelFactor_mul`, `borelFactor_one`: it is nonzero and multiplicative
  on `ℂˣ`, and `borelFactor l α 1 = 1`.
- `borelFactor_of_norm_eq_one`: on `‖z‖ = 1` it is `z^l`.
- `borelFactor_exp`: `borelFactor l α (e^s) = exp(sα)` for real `s`.
- `contDiffAt_borelFactor`: it is `C^∞` over `ℝ` near every `z ≠ 0`. Negative powers are
  handled as inverses of positive powers.

### The Borel character

- `borelChar l α M` (definition): `∏ⱼ borelFactor (l j) (α j) (M j j)` for a matrix `M`, that is,
  `∏ⱼ (M_jj/‖M_jj‖)^{l_j} ‖M_jj‖^{α_j}`.
- `diag_ne_zero_of_upper`: an invertible upper triangular matrix `M` (`IsUnit M`) has nonzero
  diagonal entries. This is the Library lemma
  `Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper` (module
  `Langlands.Group.GL.UpperBruhatCoordinatesProof`), stated for elements of `GL_n`, applied to the
  unit `hu.unit` whose underlying matrix is `M`.
- `borelChar_mul`: `borelChar` is multiplicative on upper triangular matrices with nonzero
  diagonal entries. The diagonal of a product of upper triangular matrices is the product of the
  diagonals; this is the Library lemma `Langlands.IntegerLattice.GlobalBlockBasis.upper_mul_diag`
  (module `Langlands.Representation.IntegerLattice.GeneralizedWeightGlobalBasisProof`), which
  `borelChar_mul` and `borelChar_diagonalUnits_mul` use.
- `borelChar_one`, `borelChar_ne_zero`: `borelChar l α 1 = 1`, and `borelChar` is nonzero when the
  diagonal entries are nonzero.
- `borelChar_of_norm_diag`: if all diagonal entries have norm `1`, `borelChar l α M = ∏ⱼ M_jj^{l_j}`.
- `contDiffAt_borelChar`: `borelChar l α` is `C^∞` over `ℝ` near every matrix with nonzero
  diagonal entries.
- `borelChar_diagonalUnits_mul`: for `a : Fin n → ℂˣ`, `u` in the Library's `upperUnipotent n ℂ`
  and `M` upper triangular with nonzero diagonal,
  `borelChar l α (diag(a) · u · M) = (∏ⱼ borelFactor (l j) (α j) (a j)) · borelChar l α M`.

### Complex characters and the principal series character

- `borelFactor_eq_unitChar`: `borelFactor l α z = unitChar l (α/2) z`, where `unitChar μ w z =
  (z/‖z‖)^μ exp(2w log ‖z‖)` is the Library's factor (module
  `Langlands.Representation.Archimedean.ComplexStandardNontrivialProof`).
- `posWeight_ofFn`, `posExponent_ofFn`: for `d : Fin n → ComplexCharacterData`, the Library's
  position weight `posWeight (List.ofFn d) j` and position exponent `posExponent (List.ofFn d) j`
  (same module) are `(d j).weight` and `(d j).exponent`. Both are proved by induction on `n`.
- `principalSeriesCharacter_ofFn`: for `d : Fin n → ComplexCharacterData` and `a : Fin n → ℂˣ`,
  `principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d)) a` equals
  `∏ⱼ borelFactor (d j).weight (2 (d j).exponent + (n − 1) − 2j) (a j)`. This is the Library
  theorem `Langlands.Archimedean.principalSeriesCharacter_eq` (module
  `ComplexStandardNontrivialProof`), which writes the left side as
  `∏ⱼ unitChar (posWeight ds j) (posExponent ds j + (n − 1)/2 − j) (a j)`, rewritten with the three
  lemmas above. So the principal series `complexStandardModule n (List.ofFn d)` transforms on the
  left under `diag(a) u` by the Borel character with `l_j = (d j).weight` and
  `α_j = 2 (d j).exponent + (n − 1) − 2j`.
- `characterOfParams l t` (definition): the `ComplexCharacterData` with character
  `z ↦ (z/‖z‖)^l ‖z‖^{2t}` (that is, `borelFactor l (2t)`), weight `l` and exponent `t`;
  `characterOfParams_weight` and `characterOfParams_exponent` record the last two fields.

`characterOfParams_eta` recovers the original complex character datum from its weight and exponent.
