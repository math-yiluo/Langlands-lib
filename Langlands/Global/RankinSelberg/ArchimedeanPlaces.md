# Archimedean places for the global Rankin–Selberg integrals

Module `Langlands.Global.RankinSelberg.ArchimedeanPlaces`, namespace
`Langlands.Global.RankinSelbergGlobal`. This is a helper module for the archimedean statements
`ArchimedeanFunctionalEquationStatement`, `ArchimedeanFactorizationStatement` and
`ArchimedeanCentralSignStatement`. It contains definitions and two specification lemmas, and
no statements.

## Definitions

### Inclusions of one infinite place

The Library writes the archimedean component of `GL_n(𝔸_F)` as `ArchimedeanGL F n`, the units
of `n × n` matrices over the mixed space `F_∞ = ℝ^(r₁) × ℂ^(r₂)`
(`mixedEmbedding.mixedSpace F`). The real coordinate at a real place `v` and the complex
coordinate at a complex place `w` are those of the mixed space. At a complex place this is
the identification `InfinitePlace.Completion.ringEquivComplexOfIsComplex`, which the
Library's `IsComplexAdditiveComponent` and the place actions also use.

* `placeMatrixHom F n`: the multiplicative map that assembles a real matrix at every real
  place and a complex matrix at every complex place into one matrix over `F_∞`, entry by
  entry.
* `placeGL F n : ∏_(v real) GL_n(ℝ) × ∏_(w complex) GL_n(ℂ) →* ArchimedeanGL F n`: its
  restriction to invertible matrices.
* `realPlaceGL F n v : GL_n(ℝ) →* ArchimedeanGL F n`: `g` at the real place `v`, the identity
  at every other infinite place.
* `complexPlaceGL F n w : GL_n(ℂ) →* ArchimedeanGL F n`: the same at the complex place `w`.
* `adelicPoint F n g a`: the point of `GL_n(𝔸_F)` (the Library's `Points F n`) with
  archimedean component `g ∈ ArchimedeanGL F n` and finite component
  `a ∈ FiniteAdelicGL F n`. It is assembled with `AdelicGL.pair` and the Library's
  coordinate equivalences `archimedeanGLCoordinates` and
  `GeneralLinearGroupPoints.adelicEquiv`.
* `realPlacePoint F n v g = adelicPoint F n (realPlaceGL F n v g) 1`, the adelic point
  `ι_v(g)`; `complexPlacePoint F n w g` is the same at a complex place.
* `finitePoint F n a = adelicPoint F n 1 a`, the adelic point of a finite adelic matrix.

### Archimedean restrictions of global Whittaker functions

Let `T` be a cuspidal realization of `GL_(r+1)` (`Automorphic.CuspidalOperatorRealization`)
and `χ` an additive character of `𝔸_F`. Write `W_x = cuspWhittaker F T χ x` for the global
Whittaker function of `x ∈ T.Space`.

* `IsRealPlaceWhittaker F T χ v W`, for `W : GL_(r+1)(ℝ) → ℂ`, holds if there are
  `x ∈ T.Space` and `a ∈ FiniteAdelicGL F (r+1)` with
  `W(g) = W_x(ι_v(g) · a)` for all `g`, where `a` stands for `finitePoint F (r+1) a`.
* `IsComplexPlaceWhittaker F T χ w W`, for `W : GL_(r+1)(ℂ) → ℂ`, is the same at a complex
  place `w`.

This is the second formulation that the task allows: archimedean restrictions
`g_v ↦ W(g_v a)` of the global Whittaker functions, with `a` a finite adelic point. The
components of `g` at the other infinite places are `1`. Why these functions lie in the
Whittaker models of Jacquet's Theorem 2.1 is explained in the Markdown of
`ArchimedeanFunctionalEquationStatement`.

### The scalar of the central element `−1` at an infinite place

* `realMinusOneScalar T v`: if there is `c ∈ ℂ` such that the compact action
  `T.realization.realPlaceCompactRepresentation v (−1)` of `−1 ∈ O(r+1)` at the real place
  `v` is multiplication by `c` on all of `T.Space`, it is such a `c` (chosen); otherwise it
  is `1`.
* `complexMinusOneScalar T w`: the same for `−1 ∈ U(r+1)` and the compact action
  `complexPlaceCompactRepresentation` at the complex place `w`.

`realMinusOneScalar_spec` and `complexMinusOneScalar_spec` state that, when `−1` acts by
some scalar, it acts by the defined one. Such a scalar is unique, because `T.Space` is
nonzero (`CuspidalOperatorRealization.space_nontrivial`). These are the scalars `ω'_v(−1)`
of the statements: the central character of the archimedean component at `v`, evaluated
at `−1`.

**Why `−1` acts by a scalar.** The element `−1` is central in `GL_(r+1)(F_v)`, so its action
commutes with the action of `GL_(r+1)(𝔸)` on automorphic forms. Its square is `1`, so
`T.Space` is the sum of its `+1` and `−1` eigenspaces. Both are invariant, and `T` is
irreducible, so one of them is zero. The definition does not rely on this argument: the
value `1` is used only if `−1` does not act by a scalar.

## Choices of form

* **Mixed coordinates.** The inclusions go through the Library's mixed space, not through
  the completions `InfiniteCompletion F v`. The global integrals and the additive
  components `IsRealAdditiveComponent`, `IsComplexAdditiveComponent` use the same
  coordinates.
* **Scalars by choice.** The minus-one scalars are defined quantities (by `Classical.choose`
  when they exist), as the task requires, not existential ones.
* The module declares two local instances: affineness and smoothness of the group scheme
  `GL_n`, by `GroupScheme.GeneralLinear.isAffine_groupScheme` and
  `GroupScheme.GeneralLinear.smoothStatement`. The global modules of the Library declare the
  same instances.

## Sources

* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg` (PDF page = printed page), p.4: the Whittaker
  models `W(π_(σ,u) : ψ)` of the archimedean components.
* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), pp.216–217: the
  archimedean central characters `ω'_v` in the sign `ω'_v(−1)^(n−1)` of Theorem 3.6; p.220:
  their product over all places.

## Provenance

Internal helper definitions of Task 7136, written for the three archimedean statements.
The inclusions and restrictions realize the source's `W_v(g_v) = W(g_v a)` in the
coordinates of the Library.
