# Pointed etale torus lifting from a supplied universal family

Author: Worker 606.

`Langlands.GroupScheme.TorusSubgroupModuli.pointedTorusLift.{u}` constructs
actual pointed etale lift data for a closed relative torus in a residue fibre
of an arbitrary group scheme `G/S`. Its input includes an actual parameter
scheme `M/S`, a group scheme `K/M`, and a homomorphism `j : K ⟶ G_M` satisfying
`IsClosedSubgroup j`, `RelativeTorus.IsTorus K`, and
`TorusSubgroupModuli.IsUniversal j`, with `M/S` smooth. The chosen residue-fibre
torus `T₀` need only be a relative torus over `Spec κ(s)`; it is not required
to be split. The input also specifies its actual closed inclusion `i₀` in
`G_κ(s)`. All schemes lie in the arbitrary universe `u`.

The result `PointedTorusLiftData G s T₀ i₀` contains a scheme `U`, an etale
map `p : U ⟶ S`, a point `b : Spec κ(s) ⟶ U` satisfying
`b ≫ p = S.fromSpecResidueField s`, a relative torus `T/U`, and an actual
closed inclusion `i : T ⟶ G_U`. It also supplies an actual group-scheme
isomorphism `e : T_b ≅ T₀`. Its `recovers` field states that the raw base
change of `i` followed by `Descent.pullbackComparison p b c hb G` is
`e.hom ≫ i₀`, where `c = S.fromSpecResidueField s`. This comparison is exactly
the inverse of `baseChangeCompIso p b G` followed by the equality-of-base-map
isomorphism for `hb`. Thus the field retains the full inclusion square,
including the equality of the base morphisms. Neither a surjective etale
neighbourhood map nor an affine neighbourhood is required by the data type.

The ambient `G/S` has no smoothness, affineness, separation or quasi-compactness
hypothesis here. Those conditions may be needed to obtain the supplied
universal family, whose existence is not proved by this construction. The
conclusion does not assert that the lifted torus is split, maximal, or
self-centralizing, and does not assert ambient affineness.

## Implemented construction

Apply `IsUniversal j` at `Spec κ(s)` to the literal subgroup functor
`SubgroupFunctor.range i₀`. Closedness and the relative-torus hypothesis make
it admissible. This gives an actual parameter morphism
`x : Spec κ(s) ⟶ M` for which `evaluate j x = range i₀`. The unique-parameter
part is not needed for the construction.

The published `Langlands.AlgebraicGeometry.exists_pointed_etale_section`
extends `x` to maps `a : U ⟶ M`, `p : U ⟶ S`, and `b : Spec κ(s) ⟶ U`, with
`p` etale, `a ≫ M.hom = p`, `b ≫ p = c`, and `b ≫ a = x`. Pull `K` back along
`a` to get `T`; take `familyHom j a` for its inclusion. The imported
`RelativeTorus.IsTorus.baseChange` and
`TorusSubgroupModuli.isClosedSubgroup_familyHom` give its torus property and
closedness.

The evaluation at `x` and the inclusion `i₀` represent the same subgroup
functor. Both are monomorphisms because they are closed immersions.
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` therefore supplies
`e₀ : K_x ≅ T₀`, and its `isoOfIsRepresentedBy_hom_comp` lemma gives equality
with the original inclusion. Compose `e₀` with the actual comparison
`(K_a)_b ≅ K_x` from `b ≫ a = x` to get `e`.

The imported helper `familyHom_original` proves that evaluation preserves the projection
to the original ambient scheme. The helper `familyHom_comparison` then
compares successive evaluation along `a` and `b` with direct evaluation along
`x`, using actual source and target pullback comparisons. Its proof forgets
to schemes and checks both pullback projections: the original ambient
projection follows from `familyHom_original` and the pullback-comparison projection
lemma, and the base projection is the equation for a morphism over the base.
This comparison and the inclusion equality for `e₀` prove the `recovers` field.
The existence theorem `nonempty_pointedTorusLiftData` constructs all these
fields, and `pointedTorusLift` uses classical choice to select the data.

## Internal provenance

This is an internal composition of the published universal-family definitions
in `Langlands.GroupScheme.HomScheme.TorusSubgroupModuli`, the represented-
subgroup comparison in `Langlands.GroupScheme.RepresentedSubgroup`, the
actual pullback comparisons in `Langlands.GroupScheme.Descent.Data`, and the
published pointed etale local-section construction. It introduces no new
literature theorem or unproved representability input. Its intended consumer
is `Langlands.GroupScheme.ReductiveFiberAffinenessStatement`; the required
existence of smooth torus-subgroup moduli without ambient affineness remains
a separate prerequisite.

The projection helper is reused from [`SubgroupFamilyEvaluation`](../HomScheme/SubgroupFamilyEvaluation.md).
