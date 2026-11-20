# Complex-place parameters under twists by arbitrary Hecke characters

Module `Langlands.Automorphic.ComplexPlaceParameterHeckeTwist`. Author: Worker 5086
(Task 7783). Internal helper results; no source is cited.

The Library's complex-place parameter `OperatorRealization.HasComplexPlaceParameter v ds`
(module `Langlands.Automorphic.ArchimedeanPlaceParameter`) asks for an injective linear map
from the `U(n)`-finite functions of the complex standard module of `ds` (the smooth principal
series of the block characters) into the realization, carrying right translation by `U(n)`
to the compact action at `v` and the right derivative along `X ∈ 𝔤𝔩_n(ℂ)` to the Lie action of
`1 ⊗ X` at `v`. The published `HasComplexPlaceParameter.heckeDeterminantTwist`
(`AssociatedGammaAutomorphicTwist`) treats only twists by characters trivial at infinity.
This module removes that restriction.

## Results

In namespace `Langlands.Automorphic.ComplexPlaceHeckeTwist`:

- `exists_hasComplexPlaceParameter μ v`: every Hecke character `μ` has a parameter at every
  complex place `v`, namely the published polar data
  `HeckeFunctionalEquation.complexCompletionCharacterData` of its local character (whose
  coordinate `ringEquivComplexOfIsComplex` is the same `extensionEmbedding` used by
  `HeckeCharacter.HasComplexPlaceParameter`).
- `HasComplexPlaceParameter.mul`: if `μ, μ'` have parameters `d, d'` at `v`, then `μ * μ'` has
  `d.mul d'`.
- Mixed coordinates (section `Mixed`): `mixedSingle v z` is the mixed-space element equal to
  `z` at `v` and `1` elsewhere; `placeMatrix n v Y` is the archimedean matrix equal to `Y` at `v`
  and the identity elsewhere, an affine function of `Y` with linear part `placeLinear n v`
  (`placeMatrix_eq`, `hasFDerivAt_placeMatrix`), and `placeLinear_eq` identifies the linear
  part with the published inclusion `complexPlaceLieInclusion F n v` of the Lie algebra at `v`.
  `det_placeMatrix`: `det (placeMatrix n v Y) = mixedSingle v (det Y)`.
- `unitsCharacterExtension_mixedSingle`: if `μ` has parameter `d` at `v`, the published
  archimedean character `μ.mixedCharacter`, extended by zero off the units, takes at
  `mixedSingle v z` the value `d.character z` (also extended by zero). The proof identifies
  the unit with the infinite idele of `v` (`ringEquiv_mixedSpace_ofCompletion`,
  `infiniteIdelesInclusion_ofCompletion`).
- `adelicDeterminant_complexPlaceCompactInclusion`: on the unitary group at `v`, embedded by
  the published `complexPlaceCompactInclusion`, `μ ∘ det` equals `detCharacter d.character`
  (`η ∘ det` on `GL_n(ℂ)`).
- `characterDifferential_complexPlaceLieInclusion`: the published derivative at `1` of the
  archimedean determinant character of `μ`, along `complexPlaceLieInclusion F n v X`, equals
  the right derivative at `1` of `detCharacter d.character` along `X`. Proof: the published
  `smoothDifferential_eq_of_extension` computes the left side with the extension
  `characterExtension n μ M = unitsCharacterExtension μ.mixedCharacter (det M)`;
  `characterExtension_placeMatrix` shows that composed with `placeMatrix n v` it is the
  units-extension of `η ∘ det`; the chain rule with `hasFDerivAt_placeMatrix` and the published
  `rightDerivative_eq_fderiv` give the equality.

In namespace `Langlands.Automorphic.OperatorRealization`:

- `HasComplexPlaceParameter.heckeDeterminantTwist_of_positionCharacter`: if `S` has parameter
  `ds` at `v`, `μ` has parameter `d` at `v`, `ds'.length = n`, and the position characters of
  `ds` are those of `ds'` times `d⁻¹`, then `S.heckeDeterminantTwist μ` has parameter `ds'`.
  The new map is `e ∘ A ∘ N`, where `A` is the given map, `N` is multiplication by
  `(d⁻¹) ∘ det` (`kFiniteDetMul` of the local module) and `e` is the published
  `heckeDeterminantTwistEquiv`. Write `η = d.character`. Injectivity is that of the three factors. For `k ∈ U(n)`,
  `kFiniteDetMul_rightTranslation` and the compact equivariance of `A` give
  `A (N (R_k f)) = η(det k) · S.compact_v(k) (A (N f))`, and the published
  `heckeDeterminantTwistEquiv_compact` with `adelicDeterminant_complexPlaceCompactInclusion`
  supplies the same factor on the twisted side. For `X`, `kFiniteDetMul_rightDerivative` with
  `rightDerivative_detCharacter_inv` gives `N (R_X f) = R_X (N f) + c_X · N f` with
  `c_X = R_X(η ∘ det)(1)`; the published `heckeDeterminantTwistEquiv_differential`,
  `envelopingShift_generator` and `characterDifferential_complexPlaceLieInclusion` show that
  the twisted Lie action of `1 ⊗ X` is `e (S.Lie_v(1 ⊗ X) x + c_X · x)`. This declaration is
  compiled with `set_option maxHeartbeats 1600000`.
- `HasComplexPlaceParameter.heckeDeterminantTwist_mul` (**twist rule**): the case
  `ds' = ds.map (·.mul d)`.
- `isDeterminantMultiple_heckeDeterminantTwist`: the twist is the determinant multiple;
  `IsDeterminantMultiple.eq_heckeDeterminantTwist_inv`: if `T` is the determinant multiple of
  `S` by `χ` then `S = T.heckeDeterminantTwist χ⁻¹` (published uniqueness
  `IsDeterminantMultiple.eq` and `heckeDeterminantTwist_heckeDeterminantTwist_inv`).
- `IsDeterminantMultiple.hasComplexPlaceParameter` (**untwisting**): if `T` is the determinant
  multiple of `S` by `χ`, `T` has parameter `ds` at `v` and `χ⁻¹` has parameter `e` at `v`,
  then `S` has `ds.map (·.mul e)`.

In namespace `Langlands.Automorphic.CuspidalOperatorRealization`:
`hasComplexPlaceParameter_heckeDeterminantTwist_mul`, the twist rule for the class of an
actual cuspidal realization.

The parameter is a property of the ordered list `ds`; the results keep the order of the blocks.
