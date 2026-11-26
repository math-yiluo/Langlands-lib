# Real-place parameters under twists by complex powers of the norm

Module `Langlands.Automorphic.RealPlaceParameterNormPowerTwist`. Internal helper results; no
source is cited.

The Library's real-place parameter `OperatorRealization.HasRealPlaceParameter v ds` (module
`Langlands.Automorphic.ArchimedeanPlaceParameter`) asks for an injective linear map from the
`O(n)`-finite functions of the real standard module of `ds` into the realization, carrying
right translation by `O(n)` to the compact action at the real place `v` and the right
derivative along `X ∈ 𝔤𝔩_n(ℝ)` to the Lie action of `1 ⊗ X` at `v`. The published
`HasRealPlaceParameter.heckeDeterminantTwist` (module `AssociatedGammaAutomorphicTwist`)
treats only twists by Hecke characters trivial at infinity. This module treats the twist by the
complex power `‖·‖^s` of the idelic norm (`HeckeCharacter.normPower F s`), for every complex
`s`. The complex-place analogue, for arbitrary Hecke characters, is the module
`ComplexPlaceParameterHeckeTwist`, whose structure this module follows.

## Results

In namespace `Langlands.Automorphic.RealPlaceNormPowerTwist`:

- `normPower_adelicDeterminant`: `‖·‖^s ∘ det` at `g ∈ GL_n(𝔸)` is
  `exp (s log ‖det g‖)`, with the actual determinant norm
  `AdelicBlockDeterminantCharacter.determinantNorm` (by `HeckeCharacter.normPower_apply` and
  `IdeleAbsoluteValue.ideleClass_class`).
- `determinantNorm_ofInfinite_realPlaceGL`, `normPower_adelicDeterminant_realPlaceGL`: at the
  infinite matrix `ι_v(g)` (`RankinSelbergGlobal.realPlaceGL`), the determinant norm is
  `|det g|` and `‖·‖^s ∘ det` is `|det g|^s = RealLinkedJacquetStages.detPow n s g`. The norm
  is the published `RealPlaceRestriction.detNorm_realPlacePoint`.
- `normPower_adelicDeterminant_compact`: `‖·‖^s ∘ det` is `1` on the standard infinite compact
  subgroup. The character `k ↦ ‖det k‖` (`‖·‖^1 ∘ det`) of this compact group has positive
  real values and, by `Langlands.norm_eq_one_of_compact_quotient`, absolute value `1`; so
  `‖det k‖ = 1`.
- Mixed coordinates (section `Mixed`): `realPlaceMatrix n v Y` is the archimedean matrix equal
  to `Y` at `v` and the identity elsewhere; `coe_realPlaceGL` identifies it with the matrix of
  `ι_v(g)` for invertible `Y = g`; it is affine in `Y` with linear part `realPlaceLinear n v`
  (`realPlaceMatrix_eq`, `hasFDerivAt_realPlaceMatrix`), and `realPlaceLinear_eq` identifies
  the linear part with the inclusion `realPlaceLieInclusion F n v` of the Lie algebra at `v`.
- `characterExtension_realPlaceMatrix_eventuallyEq`: near the identity, the published extension
  `ComplexPlaceHeckeTwist.characterExtension n (normPower F s)` of the archimedean determinant
  character, composed with `realPlaceMatrix n v`, equals the extension by zero
  `unitsExtension (detPow n s)` of `|det|^s` on `GL_n(ℝ)`. On invertible matrices this is
  `normPower_adelicDeterminant_realPlaceGL`.
- `characterDifferential_realPlaceLieInclusion`: the derivative at `1` of the archimedean
  determinant character of `‖·‖^s` along `realPlaceLieInclusion F n v X` equals
  `rightDerivative (matrixModel ℝ n) X (detPow n s) 1`. The left side is computed with the
  published `smoothDifferential_eq_of_extension` and the extension above, the right side with
  `rightDerivative_eq_fderiv`; the chain rule with `hasFDerivAt_realPlaceMatrix` and
  `realPlaceLinear_eq` matches the two.

In namespace `Langlands.Automorphic.OperatorRealization`, with
`E = S.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F s)`:

- `heckeDeterminantTwist_normPower_realPlaceCompact`: `E` intertwines the compact actions at
  the real place `v`. By the published `heckeDeterminantTwistEquiv_compact` the twisted action
  differs by the factor `‖det k‖^s`, which is `1`.
- `heckeDeterminantTwist_normPower_realPlaceLie`:
  `E (Lie_v(1 ⊗ X) x + c_X x) = Lie'_v(1 ⊗ X) (E x)` with `c_X = R_X(|det|^s)(1)`. By the
  published `heckeDeterminantTwistEquiv_differential` the twisted action of an enveloping
  element `u` is `E ∘ S(θ u)`, for the shift `θ = heckeEnvelopingShift n (normPower F s)`;
  `envelopingShift_generator` and `characterDifferential_realPlaceLieInclusion` give
  `θ(1 ⊗ X) = 1 ⊗ X + c_X`.
- `HasRealPlaceParameter.heckeDeterminantTwist_normPower` (**twist rule**): if `S` has the
  parameter `ds` at the real place `v`, then `S.heckeDeterminantTwist (normPower F s)` has the
  parameter `ds.map (RealComplexTwist.realBlockComplexTwist s)`, the blocks of `ds` with `s`
  added to every exponent. The new map is `E ∘ A ∘ N`, where `A` is the given map and
  `N = (RealComplexTwist.twistEquiv s ds hr).symm` is multiplication by `|det|^(-s)` from the
  twisted standard module to the original one (module `RealStandardComplexTwist`). Injectivity
  is that of the three factors. Compact equivariance combines
  `twistEquiv_symm_rightTranslation`, the equivariance of `A` and the compact lemma above. For
  `X`, `twistEquiv_symm_rightDerivative` gives `N (R_X f) = R_X (N f) + c_X N f`, and the Lie
  lemma above absorbs the scalar `c_X`. The total rank is kept
  (`realRank_map_realBlockComplexTwist`).

In namespace `Langlands.Automorphic.CuspidalOperatorRealization`:
`hasRealPlaceParameter_heckeDeterminantTwist_normPower`, the twist rule for an actual cuspidal
realization, whose twist has realization `S.realization.heckeDeterminantTwist`.

The parameter is a property of the ordered list `ds`; the twist rule keeps the order of the
blocks. The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
