# The automorphic `GL(1)` realization of a Hecke character

Module `Langlands.Automorphic.RankOneHeckeRealization`. Author: Worker 5086 (Task 7783).
These are internal helper results and cite no source. The module sets `autoImplicit false` and
`backward.isDefEq.respectTransparency false`. It declares the `AddCommGroup` instances of the
automorphic function spaces locally, as the published realization modules do.

Throughout, `F` is a number field and `χ : HeckeCharacter F`. The rank index `0` stands for
`GL_1`.

## The standard module of the trivial block (namespace `RankOneHecke`)

- `diagonalUnits_determinant`: a matrix `g` of `GL_1(ℂ)` is the diagonal matrix of its
  determinant.
- `principalSeriesCharacter_trivial`: the principal-series character of the one-block list
  `[ComplexCharacterData.trivial]` is trivial.
- `eq_of_mem_trivialStandardModule`: every function `f` of
  `complexStandardModule 1 [trivial]` satisfies `f g = f 1`. Apply the left-equivariance of the
  principal series to `g = diag(det g) · 1 · 1`.

## The constant line (namespace `ConstantFunctions`)

`realization_one_hasComplexPlaceParameter v`: the published constant realization
`ConstantFunctions.realization F 1` has the parameter `[ComplexCharacterData.trivial]` at every
complex place `v`, in the sense of the published `OperatorRealization.HasComplexPlaceParameter`.
The injection sends a `U(1)`-finite function `f` of the trivial standard module to the constant
`f 1`, through the published `scalarEquiv`. It is injective because such functions are
constant. Compact translations act trivially on both sides. The right derivative of a constant
function is `0`, and so is the augmentation of a Lie generator.

## The `GL(1)` realization (namespace `RankOneHecke`)

- `trivial_mul`: `trivial.mul d = d`.
- `cuspidal χ : CuspidalOperatorRealization F 0` is the published
  `(ConstantFunctions.rankOneCuspidal F).heckeDeterminantTwist χ`, the constant cusp line
  multiplied by `χ ∘ det`. `presentation χ` is the published twisted constant spectral
  presentation `(ConstantFunctions.rankOneSpectralPresentation F).heckeDeterminantTwist χ`.
  Both need `[CompactSpace (AdeleQuotient F)]`.
- `cuspidal_hasComplexPlaceParameter`: if `χ.HasComplexPlaceParameter v d`, then
  `(cuspidal χ).isoClass.HasComplexPlaceParameter v [d]`. This follows from the twist rule
  `CuspidalOperatorRealization.hasComplexPlaceParameter_heckeDeterminantTwist_mul` (module
  `ComplexPlaceParameterHeckeTwist`, candidate `78761ac6`) applied to the trivial parameter of
  the constant line, together with `trivial_mul`.
- `presentation_eulerPolynomial`: outside the exceptional set, the Euler polynomial of
  `presentation χ` at `v` is `1 - χ_v(ϖ_v) X`, where `χ_v(ϖ_v)` is the published
  `χ.finiteUniformizerValue v`. The proof combines the published
  `heckeDeterminantTwist_eulerPolynomial` (substitution `X ↦ χ_v(ϖ_v) X`) with the Euler
  polynomial `1 - X` of the trivial rank-one spectrum.

## Supercuspidality

- `LocalRealization.isSupercuspidal_rankOne`: an irreducible admissible local realization of
  `GL_1` at a finite place is supercuspidal. Its `padicObject` is supercuspidal by the published
  `RankinSelberg.HighlyRamified.isSupercuspidal_rankOne`, for the canonical topology of the
  completion. `GL_1` has no proper block parabolic.
- `presentation_localComponent_isSupercuspidal`: every local component of `presentation χ` is
  supercuspidal. The local components of the constant presentation are irreducible and
  admissible (published `tensorLocalModel_isIrreducible` and `_isAdmissible`), and twisting
  keeps both properties (`heckeDeterminantTwist_localComponent_isIrreducible_iff` and
  `_isAdmissible_iff`). This proof uses `set_option maxHeartbeats 1600000`.
- `cuspidal_hasSupercuspidalComponent χ v`: `(cuspidal χ).isoClass` has a supercuspidal
  component at every finite place `v`, witnessed by `presentation χ`.
