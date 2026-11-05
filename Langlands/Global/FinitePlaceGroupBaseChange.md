# Actual finite-completion points and rational points of the base change

Author: Worker 1624.

This derived comparison uses only the published scheme-pullback point
equivalences and regular-function evaluation topologies. Let `F : Type u`
be any number field, let `G` be an actual group scheme over `Spec F`, and
let `v` be a finite place. The universe `u` is arbitrary.

`baseChangedGroup F G v` abbreviates the actual pullback of `G` to
`Spec (FiniteCompletion F v)`. The multiplicative equivalence
`baseChangeMulEquiv F G v` is the existing `baseChangeBasePointsEquiv`.
It identifies the identity-test rational points of this pullback with the
existing `FinitePlaceGroupPoints F G v`. It uses the original group laws.
Its `_left` formula is the first projection from the actual scheme
pullback. These algebraic comparisons require no affineness assumption.

`baseChangeMulEquiv_map` proves compatibility with every actual
group-scheme morphism `p : P ⟶ G`. On the base-changed side the map is
`rationalPoints.map` of the actual pullback of `p`; on the finite-place
side it is the existing `P.affinePointsTarget p` at the finite completion.
Extensionality of relative scheme morphisms reduces the formula to the
first-projection identity for the pullback morphism.

Assume that the underlying scheme of `G` is affine. The pullback scheme
is then affine too. The source topology is precisely the published
`rationalPointTopology` at the finite completion, installed only as a
local instance in this module. The target topology is the existing
`FinitePlaceGroupPoints.topologicalSpace`, namely evaluation of all
global regular functions in the actual finite completion.

`isHomeomorph_baseChangeMulEquiv` compares the multiplicative equivalence
with a composite of two published homeomorphisms:
`rationalPointsAffineHomeomorph` on the pullback, followed by the inverse
of `affinePointsBaseChangeContinuousMulEquiv` for `F → F_v → F_v`.
Both carrier maps are the first projection of the scheme pullback,
as shown by their existing underlying-morphism formulas.
`baseChangeContinuousMulEquiv` bundles this same multiplicative
equivalence and continuity in both directions. Its application lemma
preserves the original point map.

This is an internal adapter for applying local rational-point results
to actual completion-valued points. It constructs no building, special
point, compact subgroup or Iwasawa decomposition, and by itself proves
no local existence statement.
