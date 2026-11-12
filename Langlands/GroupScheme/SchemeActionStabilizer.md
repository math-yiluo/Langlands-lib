# The stabilizer group scheme of an action

Author: Worker 4246.

Let `G` be a group scheme over a scheme `S` acting by `b : SchemeAction G Z` on a scheme `Z`
over `S` (`Langlands/GroupScheme/SchemeAction.lean`). This module makes the stabilizer scheme
of `b` into a group scheme over `Z` and shows that its fibre over any point of `Z` with values
in a one-point scheme, for example the spectrum of a field, is a closed subgroup of the
corresponding base change of `G`. All declarations are in the dedicated namespace
`Langlands.GroupScheme.ActionStabilizer` and take the action `b` as an explicit argument
(written `stab b`, `stabilizerGroup b`, and so on); no hypothesis on `G`, `Z` or `S` is assumed
except where stated. The module contains no new axioms or statements; it is internal
infrastructure for `UnipotentOrbitStabilizerSmoothReduction` (provenance: internal).

The namespace is separate from `Langlands.GroupScheme.SchemeAction` because the Library already
uses two of these names there for other constructions: `SchemeAction.stabilizer` is the
stabilizer subgroup functor of a section `𝟙_ (Over S) ⟶ X` over the base `S`
(`Langlands/GroupScheme/StabilizerClosedSubgroup.lean`), and `SchemeAction.orbitMap` is the
orbit morphism `G.X ⟶ X` of such a section
(`Langlands/GroupScheme/SchemeActionRationalPoints.lean`).
The constructions here are different: `stabilizerFunctor b` is a subgroup functor of
`G_Z = G ×_S Z` over `Z`, the stabilizer of the tautological point of `Z`, and
`baseChangeOrbitMap b q` is an orbit map over an arbitrary `q : Y ⟶ Z.left`. A module may import
both this module and those Library modules.

The file sets `backward.isDefEq.respectTransparency false` (and its `.types` variant), as
`Langlands/AbelianScheme/KernelBaseChange.lean` does, so that rewriting can pass between the
definitionally equal objects `((Over.pullback f).obj X).left`, `((GroupScheme.baseChange f).obj
G).X.left` and `pullback X.hom f`.

## The stabilizer scheme over `S`

- `graph b : G.X ⊗ Z ⟶ Z ⊗ Z` is the action graph `(g, z) ↦ (g.z, z)`, `lift b.hom (snd G.X Z)`.
- `stab b : Over S` is `pullback (graph b) (lift (𝟙 Z) (𝟙 Z))`, the base change of the graph
  along the diagonal of `Z`. `stabProj b : stab b ⟶ Z` is the second projection. This is
  literally the morphism `pullback.snd (lift b.hom (snd G.X Z)) (lift (𝟙 Z) (𝟙 Z))` of the
  published `UnipotentOrbitStabilizerSmoothStatement`, `IsStabilizerFlat` and
  `HasOrbitDimension`.
- `stabGroup b : stab b ⟶ G.X` is the first projection followed by `fst G.X Z`.
- `stab_fst`: the first projection is `lift (stabGroup b) (stabProj b)`. Its second component is
  `stabProj b` because the graph followed by `snd Z Z` is `snd G.X Z` and the diagonal followed
  by `snd Z Z` is the identity.
- `act_stabGroup_stabProj`: `b.act (stabGroup b) (stabProj b) = stabProj b`; compose the
  pullback condition with `fst Z Z`.
- `stabLift b g t h`: a point `g` of `G` and a point `t` of `Z` over the same test scheme with
  `b.act g t = t` give the point `pullback.lift (lift g t) t` of the stabilizer, with
  projections `g` and `t` (`stabLift_stabGroup`, `stabLift_stabProj`).
- `stab_hom_ext`: two points of the stabilizer with the same two projections are equal
  (`pullback.hom_ext`, using `stab_fst` for the first component).

## The group scheme over `Z`

Write `G_Z = (GroupScheme.baseChange Z.hom).obj G`. For a scheme `T` over `Z.left`, the Library
equivalence `baseChangePointsEquiv Z.hom G T` identifies the points `T ⟶ G_Z.X` with the points
`(Over.map Z.hom).obj T ⟶ G.X` and preserves products
(`Langlands/AbelianScheme/KernelBaseChange.lean`).

- `basePoint T : (Over.map Z.hom).obj T ⟶ Z` is the structure morphism `T → Z`;
  `map_basePoint` says that it is compatible with morphisms of `Z`-schemes.
- `stabilizerFunctor b : SubgroupFunctor G_Z`: a point `x` over `T` belongs to it when
  `b.act (baseChangePointsEquiv Z.hom G T x) (basePoint T) = basePoint T`. It contains `1`
  (`SchemeAction.act_one`) and is closed under products (`SchemeAction.act_mul`) and inverses
  (`g⁻¹.t = g⁻¹.(g.t) = (g⁻¹ g).t = t`). Restriction along `a : T' ⟶ T` preserves it by
  `baseChangePointsEquiv_naturality`, `map_basePoint` and `SchemeAction.naturality`.
- `stabOver b : Over Z.left` is `Over.mk (stabProj b).left`, and
  `stabIncl b : stabOver b ⟶ G_Z.X` is `pullback.lift (stabGroup b).left (stabProj b).left`.
  Its components are `stabIncl_left_fst` and `stabIncl_left_snd`.
- `toStab b y` turns a point `y : T ⟶ stabOver b` over `Z` into the point `y.left` of the
  stabilizer over `S`; its projections are `basePoint T` (`toStab_stabProj`) and the point
  of `G` corresponding to `y ≫ stabIncl b` (`toStab_stabGroup`).
- `mem_stabilizerFunctor_iff`: a point `x` of `G_Z` lies in `stabilizerFunctor b` if and only
  if it factors through `stabIncl b`. Forwards, `stabLift b` of the corresponding point of `G` and
  `basePoint T` gives the factorization, checked with `pullback.hom_ext`. Backwards, apply
  `SchemeAction.naturality` to `act_stabGroup_stabProj` along `toStab b y`.
- `stabIncl b` is a monomorphism: two points with the same image have equal `toStab b`
  (`stab_hom_ext`), hence equal underlying morphisms.
- `stabilizerGroup b : GroupScheme Z.left` is the Library's
  `SubgroupFunctor.representingGroupScheme` for `stabIncl b`
  (`Langlands/GroupScheme/RepresentabilityTransfer.lean`). Its underlying object is
  `stabOver b`, so `stabilizerGroup_hom` (`rfl`) says that its structure morphism is
  `(stabProj b).left`. `stabilizerHom b : stabilizerGroup b ⟶ G_Z` is the induced
  homomorphism, with underlying morphism `stabIncl b` (`stabilizerHom_hom`).

## Underlying schemes and the fibres

- `isPullback_stab_left`: the defining square of `stab b` stays a pullback on underlying
  schemes, because `Over.forget S` preserves pullbacks (connected limits).
- `stab_fst_left_fst`, `stab_fst_left_snd`, `stab_fst_left_act`: the components of the first
  projection on underlying schemes are `(stabGroup b).left`, `(stabProj b).left`, and its
  composite with `b.hom.left` is `(stabProj b).left`. `diag_left_fst`, `diag_left_snd`,
  `graph_left_fst`, `graph_left_snd` give the components of the diagonal and of the graph.
- Instance: if `G.X.hom` is locally of finite type, so is `(stabProj b).left`. The diagonal of
  `Z` is locally of finite type, since its composite with a projection is the identity
  (`locallyOfFiniteType_of_comp`). Its base change, the first projection of the stabilizer, is
  then locally of finite type. `(stabProj b).left` is this projection followed by
  `pullback.snd G.X.hom Z.hom`, a base change of `G.X.hom`.

Fix a morphism `q : Y ⟶ Z.left` and write `r = q ≫ Z.hom`.

- `bcMap q p : pullback p r ⟶ pullback p Z.hom` is `(x, y) ↦ (x, q(y))`, and
  `isPullback_bcMap`: `X ×_S Y` is the base change of `X ×_S Z` along `q`
  (`IsPullback.of_right` with the two defining pullback squares).
- `pointSection q : Y ⟶ Z ×_S Y` is `y ↦ (q(y), y)`, a section of the second projection.
- `baseChangeOrbitMap b q : G ×_S Y ⟶ Z ×_S Y` is `(g, y) ↦ (g.q(y), y)`.
- `fibreIncl b q : pullback (stabProj b).left q ⟶ G ×_S Y` is `(s, y) ↦ (stabGroup(s), y)`.
- `isPullback_fibreIncl`: the square with sides `fibreIncl b q`, the projection to `Y`,
  `baseChangeOrbitMap b q` and `pointSection q` is a pullback. The square from `G ×_S Y` and
  `Z ×_S Y` to `G ×_S Z` and `Z ×_S Z` (by `bcMap`) is a pullback by `IsPullback.of_bot` and
  two instances of `isPullback_bcMap`. Pasting the fibre square of `stabProj b` with
  `isPullback_stab_left` gives a pullback whose top and bottom composites equal those through
  `fibreIncl b q` and `pointSection q`. `IsPullback.of_right` then gives the claim.
- `isClosedImmersion_fibreIncl`: if `Y` has at most one point (`Subsingleton Y`), then
  `fibreIncl b q` is a closed immersion. The section `pointSection q` is a closed immersion by
  Mathlib's `isClosedImmersion_of_comp_eq_id`, and closed immersions are stable under base
  change.
- `fibreHom b q h`, for `h : q ≫ Z.hom = r'`, is the homomorphism from the base change along
  `q` of `stabilizerGroup b` to the base change of `G` along `r'`. It is the base change of
  `stabilizerHom b` followed by the Library comparison `Descent.pullbackComparison`
  (`Langlands/GroupScheme/Descent/Data.lean`). `fibreHom_left`: for `h = rfl` its underlying
  scheme morphism is `fibreIncl b q`. This follows from `pullback.hom_ext`,
  `Descent.pullbackComparison_hom_fst` and the fact that the comparison lies over `Y`.
- `isClosedSubgroup_fibreHom`: if `Y` has at most one point, `fibreHom b q h` is a closed
  subgroup (`IsClosedSubgroup`, `Langlands/GroupScheme/Reductive/Basic.lean`).

For `q = Z.left.fromSpecResidueField z`, the base change of `stabilizerGroup b` along `q` has
structure morphism `(stabProj b).left.fiberToSpecResidueField z`. So the scheme-theoretic fibre
of the stabilizer over `z` is a closed subgroup of `G_{κ(z)}`. This is the step "`H_z` is an
algebraic subgroup of `G_{κ(z)}`, closed by Milne, Proposition 1.41" in the Markdown of the
published `UnipotentOrbitStabilizerSmoothStatement`. Here the closedness is proved directly
from the rational point, without Proposition 1.41.
