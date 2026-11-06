# Finite affine cover of the actual Weil restriction

This is derived geometric infrastructure for Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 4.2, printed pages
9–10. Conrad uses the finite-type, separated integral Weil model of a
quasi-projective scheme along a finite locally free coefficient extension.
This module constructs a finite cover of the existing actual affine-chart Weil
scheme and derives its quasi-compactness. It also proves local finite type.
The hypotheses below remain explicit; separatedness of the Weil scheme and the
full adelic comparison are separate obligations.

Let `A` and `B` be commutative rings in the same arbitrary universe, with an
`A`-algebra structure on `B`, and suppose `B` is finite and projective as an
`A`-module. Let `Y` be an actual scheme over `Spec B` whose structural morphism
is locally of finite type. Write `W = affineChartWeilRestriction A B Y` for the
previously constructed scheme obtained by gluing the original affine Weil
charts. All point sets, opens and morphisms below belong to these original
schemes; their topologies are the existing scheme topologies.

`affineChartWeilRestriction_locallyOfFiniteType` proves that `W` is locally of
finite type over `Spec A`, without a compactness or separatedness hypothesis on
`Y`. The existing open cover of `W` consists of the actual affine Weil
restrictions of the affine opens of `Y`. Each structural morphism is locally of
finite type by the affine construction. The over-category commutativity law
identifies its composite with the structural map of `W`, and source locality
then gives the result.

For the finite-cover construction, assume additionally that the underlying
scheme `Y.left` is compact, that `Y.hom` is separated, and that
`HasFiniteAffineNeighborhoods Y.left` holds: every finite subset of its actual
point set lies in one affine open. The existing projective-immersion theorem
provides this last property in the intended quasi-projective setting. No
Noetherian, reducedness, separability or Hausdorff hypothesis is added.

`affineChartWeilRestrictionFiniteChartFamily` selects a finite family of original
affine opens of `Y`, using `boundedAffineNeighborhoodFamily` at the natural bound
`finiteAlgebraFiberBound A B`. This bound is chosen from finite module generators
of the original coefficient algebra, independently of any field-valued point.
The bounded-family law says that the full range of any map from a finite type
of cardinality at most this bound is contained in one selected affine open.

`affineChartWeilRestrictionFiniteChartFamily_covers` shows that every actual
point `x` of `W` lies in the image of one selected affine Weil chart. Its proof
uses the original residue field `C = W.left.residueField x`, with the `A`-algebra
structure induced by the composite from `Spec C` to `W` and then to `Spec A`.
The residue-field morphism is therefore an actual `A`-relative test point `p`.
Apply the original counit comparison to obtain a morphism `q` from its base
change to `Y`. The existing tensor-spectrum isomorphism identifies this base
change with `Spec (B tensor_A C)`. Tensor commutation and the uniform all-prime
fiber bound show that this spectrum is finite with cardinality at most the
chosen bound. This includes nonreduced coefficient fibers and empty spectra.

The bounded-family law puts the entire image in one selected original affine
open `U`. Surjectivity of the tensor-spectrum isomorphism transfers this
factorization to `q`. The relative open lift and the affine all-test representing
equivalence then give a morphism `r` from `Spec C` to the affine Weil chart of
`U`. Its composite to `W` has exactly the same counit comparison as `p`.
Injectivity of the original global comparison, which uses the separatedness
assumption on `Y`, identifies the two morphisms. Evaluation at the closed point
of `Spec C` recovers `x`, proving the coverage assertion.

`affineChartWeilRestrictionFiniteOpenCover` packages exactly these original
affine Weil charts and their open immersions as a scheme open cover. Its index
type is the subtype of the selected finite family. Each chart is affine, hence
compact. The finite open-cover compactness theorem gives
`affineChartWeilRestriction_compactSpace`; no compactness property of `W` is
assumed. Finally `affineChartWeilRestriction_quasiCompact` derives
quasi-compactness of its structural morphism from compactness of its source.
Together with the first instance, this establishes the two components of finite
type for this actual Weil scheme under the stated hypotheses. These are
intrinsic construction laws of the finite cover, rather than a completion claim
for Conrad's Example 4.2.
