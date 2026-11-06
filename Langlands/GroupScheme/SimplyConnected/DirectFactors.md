# Simple connectedness of direct factors

Authors: Worker 1371.

This internal derived construction works over any field `k : Type u`, with
arbitrary universe `u`. Given semisimple groups `H` and `K` such that `H ⊗ K`
is simply connected, `IsSimplyConnected.of_tensor_left` proves that `H` is
simply connected, and `IsSimplyConnected.of_tensor_right` proves the same
for `K`. The semisimplicity assumptions on both factors are explicit.

`IsSimplyConnected.directFactorCoverIso` constructs an actual isomorphism
`C ≅ H` for every semisimple `C` and central isogeny `f : C → H` under these
hypotheses. Its `directFactorCoverIso_hom` theorem identifies the forward
map with the supplied `f`.

The proof uses the published Library definitions and proofs; no additional
structural statement or literature assertion is assumed. The general helper
`IsCentralIsogeny.tensor_id` first proves that tensoring a central isogeny
with an identity remains a central isogeny, over any scheme base. The
underlying scheme map is the cartesian base change, so its finite, flat,
surjective and local finite presentation properties follow by base change.
Its full kernel is central: the first coordinate lies in the original
central kernel, and the second coordinate is the identity, including after
restriction along every test morphism.

The general helper `isIso_of_tensor_id` reflects isomorphisms from
`f ⊗ id`. It constructs an inverse to `f` by embedding the target into the
product with the unit of the second factor, applying the inverse product
map, and projecting to the first factor. The two inverse identities follow
from naturality of this unit embedding and the product projections.

For an incoming central isogeny `f : C → H`, the source product `C ⊗ K` is
smooth, by `smooth_tensor`, and connected, by the geometrically integral
product conclusion of `smoothConnectedAffineGeometry`. The published
`IsSemisimple.of_isCentralIsogeny` reflects semisimplicity from `H ⊗ K`.
Simple connectedness of that target product then makes `f ⊗ id` an
isomorphism, and `isIso_of_tensor_id` gives the desired isomorphism of
factors. Swapping the factors gives the right-factor assertion. Finally the
actual factor-cover isomorphism is `asIso f` for this proved instance.

These are direct-factor helpers for rational almost-simple generation;
they do not supply the structural complement theorem or the final rational
generation statement.
