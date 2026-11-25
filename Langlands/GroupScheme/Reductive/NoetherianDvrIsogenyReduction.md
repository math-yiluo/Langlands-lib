# Detecting isogenies over a noetherian affine base by DVR base changes

This module defines `IsDvrwiseIsogeny f`: every actual base change of the
specified homomorphism `f` along a map from the spectrum of a domain
discrete valuation ring is an isogeny. There are no Henselian or
residue-field closure assumptions on these test rings.

The supporting scheme lemma `isFinite_of_dvr_baseChanges` applies to an
affine morphism locally of finite type with target the spectrum of a
noetherian ring. Its hypothesis is finiteness of every base change to a
domain DVR. Given a DVR valuative square, the proof pulls the morphism
back along its bottom map. The resulting finite morphism is universally
closed, so its valuative criterion extends the generic point. Projection
to the original source gives a lift of the original square. The published
noetherian DVR valuative criterion makes the original morphism universally
closed. Affineness and local finite type then make it proper and finite.

For a homomorphism of affine groups over a noetherian affine base whose
source is locally of finite type, `finite_kernel_of_dvrwiseIsogeny` applies
this scheme lemma to its actual kernel. The kernel is a closed subgroup
of the source, hence affine and locally of finite type. Base change of
the kernel is canonically isomorphic to the kernel of the base-changed
homomorphism. The latter is finite because the base-changed homomorphism
is an isogeny.

For smooth affine groups, `isogeny_of_fibrewise_and_dvrwise` combines this
finite kernel with the published fibrewise reduction. These results are
internal consequences of the published noetherian DVR valuative criterion,
kernel base change, and fibrewise and isogeny stability lemmas. They do
not establish the DVRwise hypothesis from fibrewise isogenies, remove
the noetherian hypothesis, or prove the original arbitrary-base target.
