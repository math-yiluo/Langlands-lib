# AF representability from saturated affine opens of a finite cover

Authors: Worker 336 and Worker 1038.

Internal support for the Noetherian case of quasi-affine-source AF
representability. Worker 1038 proposed the statement and the
representability route; Worker 336 implemented the proof. This is an
internal derivation from the imported Library geometry and categorical
constructions, rather than a transcription of a literature statement.

For any scheme `S : Scheme.{u}`, let `W : Over S`, let `Y` be an algebraic
space over `S`, and let
`g : (schemeYoneda S).obj W ⟶ Y.presheaf` be finite and surjective in the
published relative morphism predicates. Assume:

> For every finite set `F` of points of `W.left`, there is an affine open
> `V` containing `F` such that `w ∈ V` and `SameImage g w w'` imply
> `w' ∈ V`.

The Prop-valued definition
`SaturatedAffineOpensRepresentation.HasSaturatedAffineNeighborhoods g`
expresses exactly this assumption. Under this assumption,
`SaturatedAffineOpensRepresentation.exists_AF_representation_of_saturated_affine_opens`
gives an actual `P : Over S` with
`PointTopology.HasFiniteAffineNeighborhoods P.left` and a natural
isomorphism from its full relative Yoneda presheaf to `Y.presheaf`.
The base and scheme universe remain arbitrary. No quasi-compactness,
quasi-separatedness, or Noetherian hypothesis is needed for this
conditional result.

The finite sets here are arbitrary finite sets of topological points,
as in `HasFiniteAffineNeighborhoods`; they are not restricted to closed
points or points over a fixed field. The saturation condition uses
exactly the published `SameImage`: two maps from one test scheme have
equal composites in the target and send one point to the two specified
source points.

`universalAffineOpen_preimage` first shows that a saturated affine source
open is the entire inverse image of its universal image subfunctor.
Saturation gives invariance on every scheme test: two test maps with
equal composites have pointwise related images, so either both factor
through the source open or neither does. The private
`mem_range_open_iff` expresses this factorization as containment of the
topological range in the open.

For `universalAffineOpen_isAffine`, the universal image is open by
`FiniteAffineUniversalNeighborhoods.universalAffineOpen_isOpenImmersion`.
The inverse-image equality identifies the inclusion square with a
pullback. Thus the restricted map from the affine open is finite and
surjective by base change. The imported unconditional
`finiteSurjectiveAffineDescent` gives an affine scheme representing this
target open subfunctor on all scheme tests.

`point_lifted_open_charts` applies the finite-set hypothesis to the range
of the source projection over the residue-field test of each point of
an arbitrary scheme test. This range is finite by
`finite_sourceProjection_range`. Containment in the chosen affine source
open implies membership of the residue-field value in its universal
image. The represented pullback of this open to the test scheme
therefore contains a point mapping to the original point. Mapping that
pullback to the affine representative gives a compatible point-lifted
open chart. `exists_representation` applies this construction to an
etale surjective atlas of `Y` and uses
`exists_representation_of_point_lifted_open_charts` to glue a scheme
representing `Y.presheaf`.

`hasFiniteAffineNeighborhoods_of_representation` proves AF for every
scheme representative `e : h_P ≅ Y.presheaf`. Full faithfulness of
relative Yoneda turns `g ≫ e.inv` into a scheme map `f : W ⟶ P`.
Finiteness and surjectivity transport across the isomorphism, and
finiteness reflects to `f`. For a finite `E ⊆ P.left`, the inverse image
`f ⁻¹' E` is finite, so it has a saturated affine neighborhood `V`.
The `SameImage` saturation transfers from `g` to the Yoneda map of `f`
by postcomposing the witness equality with `e.hom`.

Apply `universalAffineOpen_isAffine` now with the represented target
`schemeToSpace(P)`. The universal target open is the complement of
`f(W ∖ V)`. It is open because finite scheme morphisms are closed.
`OpenSubfunctorDescent.universalImage_scheme_eq_range` identifies its
presheaf with the range of the actual open subscheme inclusion. By full
faithfulness, its affine representative is isomorphic to this open
subscheme, proving that the open is affine. It contains `E`, since the
whole inverse image of `E` was placed in `V`. The final theorem combines
this AF result with the preceding representability result.

This support unit assumes the existence of the saturated affine
neighborhoods. It does not prove that hypothesis for a quasi-affine
source, the Noetherian induction supplying it, or an approximation
reduction. In particular it is not an unconditional proof of
`FiniteSurjectiveQuasiAffineSourceAFStatement`.
