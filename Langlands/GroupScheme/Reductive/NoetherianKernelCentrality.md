# Global kernel centrality from finite flat Artinian tests

This derived reduction retains one explicit, unproved local input,
`FiniteFlatArtinianKernelCentralityStatement`. For every local Artinian
commutative ring A, reductive groups G and H over Spec A, and a locally
quasi-finite flat surjective homomorphism f with finite actual kernel, this
input asserts centrality of the actual kernel inclusion if every canonical
residue kernel is central. Centrality uses all test schemes. The statement is
a Prop-valued definition, and this module does not prove it.

`central_kernel_fibres_baseChange` proves that centrality of all actual
canonical residue kernels is preserved by every affine base change. The
proof equips the target ring with the algebra structure determined by the
scheme morphism. It applies the inverse-image identity for the actual
centrality locus and the canonical kernel base-change comparison.

`isCentral_kernel_of_noetherian` derives global kernel centrality over a
noetherian affine ring from the local input. The kernel is of finite type
and its product with the source is locally noetherian. The published
Artinian centrality detector therefore reduces the claim to local Artinian
base changes. The homomorphism's local quasi-finiteness, flatness and
surjectivity persist. Each actual test kernel is affine and locally
quasi-finite over the Artinian base, hence finite by Mathlib's
`IsFinite.of_locallyQuasiFinite`. The preceding residue-locus comparison
supplies all central residue kernels required by the retained local input.
The actual kernel comparison returns centrality of the pulled-back original
inclusion, as required by the detector.

`isCentral_kernel_of_affine` removes the noetherian assumption on the base
ring. It chooses the noetherian reductive model that retains centrality of
every actual residue kernel, applies the previous theorem there, and pulls
centrality back. The actual kernel base-change isomorphism and the
isomorphism of arrows expressing exact model recovery transport the result
to the original kernel inclusion.

`centralKernelOfArtinianInput` bundles the unchanged actual kernel as a
commutative group scheme by the centrality just proved, retaining the local
input as an explicit argument. Its `toGrp` is definitionally the original
scheme-theoretic kernel.

All rings and schemes range over the same arbitrary universe. These are
conditional supporting reductions for the fibrewise central-isogeny
criterion. They do not prove the retained local Artinian input or the full
unchanged host criterion. The provenance is the published Artinian scheme
morphism detector, actual centrality loci, noetherian reductive models and
kernel transport, together with Mathlib's Artinian quasi-finite finiteness
lemma; no external structural assertion is used as a proof.
