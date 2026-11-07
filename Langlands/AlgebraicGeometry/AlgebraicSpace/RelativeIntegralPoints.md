# Integral points of algebraic spaces over a general base

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). The published Corollary 5.7 statements
(`HenselianIntegralPointsStatement`) concern algebraic spaces over the valuation ring `O`
itself. The adelic levels need them for spaces over the `S`-integers `C`, with `O` a
`C`-algebra. This module derives that form by base change. It also proves the injectivity
needed for Hausdorffness.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints`; `X` is an
algebraic space over `Spec C`.

- `changeRing_injective`: if `X` is separated and `φ : A →ₐ[C] B` is injective, change of
  coefficients `X(A) → X(B)` is injective. The equalizer of two points is cut out by a closed
  immersion `Z → Spec A` (`exists_representsEqualizer_of_relative_diag`). The map `Spec B → Spec A`
  factors through `Z`, so `Z → Spec A` is injective on global sections, hence an isomorphism
  (`IsClosedImmersion.isIso_of_injective_of_isAffine`).

For a nontrivially normed field `K`, a subring `O ⊆ K` and compatible `C`-algebra structures:

- `integralPointMap`: the map `X_O(O) → (X_O)_K(K)` for the base change `X_O` of `X` to `O`,
  which is the map of the Corollary 5.7 statements.
- `towerIso_integralPointMap`, `range_fieldValuedPointMap`: under the iterated base change
  homeomorphism, it is `fieldValuedPointMap C X (O → K)`, and the images correspond.
- `isOpen_range_fieldValuedPointMap`: **Corollary 5.7, openness, over `C`**. If `O` is the closed
  unit ball and henselian and `X` is quasi-separated and locally of finite type, the image of
  `X(O)` in `X_K(K)` is open. It is derived from the published `henselianIntegralPointsOpen`
  for `X_O`.
- `isCompact_range_fieldValuedPointMap`: **Corollary 5.7, quasi-compactness, over `C`**. If
  moreover `K` is locally compact and `X` is of finite type, the image is quasi-compact. It is
  derived from `henselianIntegralPointsCompact` for `X_O`.

Base change keeps quasi-separatedness and the atlas properties
(`IsQuasiSeparated.baseChange`, `HasAtlasProperty.baseChange`).
