# The local topology of the actual affine-chart Weil restriction

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed
pp. 9–10, especially the reduction to finite extensions of complete valued
fields on p. 10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`; PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad uses affine open neighborhoods of finite sets to reduce the local
comparison to the affine case and then applies Example 2.4. This file makes
that chart argument explicit on the actual glued representing scheme.
Its local topological ring formulation is a derived extension of the local
field step, with all additional hypotheses given below. It does not claim
the global adelic comparison.

## Actual objects and hypotheses

`A` and `B` are commutative rings in an arbitrary common universe `u`, with
an actual `A`-algebra structure on `B` and `Module.Finite A B` and
`Module.Projective A B`. The target `Y` is an actual scheme over `Spec B`,
locally of finite type. `G = affineChartWeilRestriction A B Y` is the
existing scheme obtained by gluing the actual affine Weil restrictions.
`RingPoint A G A` means actual morphisms over `Spec A` from `Spec A` to
`G`; the target carrier is the analogous actual `RingPoint B Y B`.

The algebraic base-point equivalence assumes relative separatedness of
`Y` and `HasFiniteAffineNeighborhoods Y.left`, the explicit condition that
every finite set of actual underlying points is contained in an affine
open. It reuses the previously constructed all-test representing
equivalence; no representing property is supplied as a premise here.

For the homeomorphisms, both rings have topologies making them topological
rings, both are local rings, and both satisfy `IsOpenUnits`. The topology
on `B` satisfies `IsModuleTopology A B`. The source and target carry their
independently defined `schemePointTopology`; neither topology is transported
through the desired equivalence. On affine schemes these agree with the
published evaluation topology.

No characteristic, separability, valued-field, completeness or nonzero
rank premise is used in this derived formulation. Finite type of `Y` is
not required beyond the stated local finite type condition.

## Tensor-unit transport and the actual map

`weilRestrictionTensorUnitTestIso` is the actual isomorphism over `Spec B`
from `Spec B` to the test scheme `Spec (B ⊗[A] A)`, induced by tensor
multiplication and its inverse. The two inverse laws follow from the
algebra-equivalence composition identities and functoriality of spectrum.
`weilRestrictionBaseTestIso` composes it with the existing actual spectrum
identification for base change, giving
`ringTest B B ≅ ringBaseChange A B (ringTest A A)`.

`affineChartWeilRestrictionBasePointComparison` first uses this test
isomorphism and then the actual glued counit comparison. This is the
canonical point map supplied by restriction of scalars.
`affineChartWeilRestrictionBasePointEquiv` is the actual all-test
equivalence at `Spec A`, followed by transport along that test isomorphism.
Its forward function is definitionally the specified comparison.

`affineWeilRestrictionComparison_basePoint` proves that on an affine target
this comparison equals the existing `affineWeilRestrictionPointHomeomorph`.
The proof uses the affine comparison formula, naturality of actual affine
point coordinates under a ring map, and the tensor-unit coordinate formula.
`affineChartWeilRestrictionBasePointComparison_chart` then identifies the
map on each actual Weil chart with the affine homeomorphism followed by
the original target open inclusion.

## Implemented topology proof

`exists_affineChartWeilRestrictionPoint` needs only that `A` is local,
beyond the algebraic construction hypotheses. Joint surjectivity of the
actual scheme chart inclusions chooses a chart containing the image of
the closed point of `Spec A`. Every point of this spectrum specializes to
its closed point, so the whole image lies in that open chart. The actual
open-immersion lift factors the scheme morphism; its factorization identity
and the base equation make the lift a genuine relative point.

`continuous_affineChartWeilRestrictionBasePointComparison` uses this
factorization for each source point. Actual open immersions induce open
embeddings on points for the local ring and open-unit hypotheses. The
independent point topology on each affine Weil chart equals its evaluation
topology. The chart formula identifies the comparison restricted to that
chart with the composite of the affine homeomorphism and the original
affine chart inclusion. This composite is continuous. The open embedding
transfers continuity at the lifted point to continuity at the given point.
Neither relative separatedness nor the finite-neighborhood condition is
needed for this forward continuity assertion.

`affineChartWeilRestrictionBasePointEquiv_symm_chart` identifies the inverse
on every original target affine chart. Applying the existing equivalence
to both sides reduces the identity to the forward chart formula and the
affine homeomorphism's inverse law.
`continuous_affineChartWeilRestrictionBasePointEquiv_symm` factors every
`B`-point through an affine open using locality of `B`. The inverse chart
formula expresses the restricted inverse as the inverse affine
homeomorphism followed by the actual Weil chart inclusion. The same open
embedding criterion transfers continuity at each lifted target point.

`affineChartWeilRestrictionPointHomeomorph` packages the actual equivalence
and both continuity proofs. Its apply lemma records exactly the original
counit comparison as its forward function.

## Actual projective-immersion specialization and scope

`projectiveImmersionWeilRestrictionPointHomeomorph` assumes an actual
immersion `i : Y.left ⟶ ProjectiveSpace B n` with
`i ≫ projectiveSpaceToSpec B n = Y.hom`. The existing geometric adapter
proves relative separatedness and finite-set affine neighborhoods from
this immersion, using actual ampleness of projective `O(1)`. Thus the
specialization requires neither of those conclusions as a separate input.
Its apply lemma again identifies the forward function with the actual
counit comparison.

This constructs the local-ring comparison needed for the local field step
of Example 4.2, under the explicit topology hypotheses. It does not yet
instantiate these hypotheses at all arithmetic completions, decompose the
finite extension into the product over places, identify integral models,
or pass to the adelic direct limit. Finite type, separatedness and
quasi-projectivity of `G` are also separate geometric obligations. These
remaining parts of Example 4.2 and the whole-paper task are retained.
