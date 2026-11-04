# Open arithmetic stages in actual field-scheme adelic points

`Langlands.Global.AdelicSpreadStageOpenStatement` asserts that an actual
arithmetic stage maps continuously and openly into actual full-adele points
of the field scheme. When the source arithmetic model is separated, the
same map is an open embedding. The topology on the field-point target may
come from a separately specified finite-type spread over a different
finite place set.

For the source model `M` over the actual outside-`S` integer ring, the stage
is indexed by any finite superlevel `T`. Its carrier is the actual relative
scheme points over `curvePlaceAdeleLevelOver k F S T` or
`numberFieldAdeleLevelOver K S T`, and its topology is the existing
fixed-model stage topology. That topology transports the arithmetic
product-of-local-points topology of the model pulled back to `T`.
The map first applies `RingPoint.changeRing` along the literal inclusion
of that level into the full adele ring. It then applies the generic-fiber
point equivalence and postcomposes with the specified isomorphism to `Y`.
Thus its target is the actual field-scheme point space
`CurvePlaceAdelePoints k F Y` or `NumberFieldAdelePoints K Y`.

The independent model `N` over the outside-`U` integer ring, and its
specified generic-fiber isomorphism to the same `Y`, supply precisely the
existing spread topology on the target. Both `M` and `N` are finite type,
expressed by local finite type and quasi-compactness of their structure
maps. No affine or separation premise is imposed on either model for
continuity and openness. The last clause assumes `IsSeparated M.hom`,
which is separation of the source arithmetic model, to obtain injectivity
and an open embedding. It does not assert injectivity of a stage of an
arbitrary model merely from separation of its generic fiber.

The function-field clause retains arbitrary perfect constants, the
specified rational-function action and scalar tower, and potentially
inseparable extensions. It adds no finite-constant or compactness premise.
All finite sets, including empty initial sets, are permitted. The
number-field clause uses full adeles and retains every infinite factor.
All declarations quantify an arbitrary common universe `u`. Existence of
the models and generic-fiber isomorphisms is explicit data.

## Source and derivation

Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.8, proves the continuous open transition maps of Theorem 3.6
and their injectivity for separated arithmetic models. Printed p.9,
Section 4, describes open quotient images in the final topology and
asserts that the adelic points of a separated arithmetic model form an
open subset of the adelic points of its generic fiber.

The present target is a derived formulation using the fixed-model point
comparison and specified generic-fiber equivalence. Apply
`AdelicFixedModelColimitOpenStatement` and compose with the defining
spread point homeomorphism. Equality of topologies from
`AdelicSpreadTopologyIndependenceStatement` then replaces the target
spread by the independently supplied one. The unrestricted-model
continuous/open clause and the arbitrary-perfect-constant extension are
derived scope; separation is retained exactly where injectivity is
asserted.

The same-spread case `S = U`, `M = N`, `e = f` and the initial superlevel
recovers the source's open-subset assertion for a separated specified
spread. This target adds the actual field-point comparison and arbitrary
independent target-spread topology to the existing fixed-model stage
target. It does not assert existence of separated spreads or eventual
separation of arbitrary spreads. This pair supplies a proposition
interface; its proof and whole-paper completion remain separate.
