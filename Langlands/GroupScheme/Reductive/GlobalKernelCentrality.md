# The global criterion from finite flat local Artinian centrality

This derived module retains the explicit, unproved
`NoetherianKernelCentrality.FiniteFlatArtinianKernelCentralityStatement`.
It extends the existing affine reduction to arbitrary scheme bases and
derives the unchanged fibrewise central-isogeny criterion from that one
local input. It does not prove the input or the unconditional criterion.

`isCentral_of_openCover` detects all-test centrality on any open cover of
the base. After an arbitrary restriction of a test scheme, its pullback of
the cover detects equality of morphisms. On each member, the actual
base-change point equivalences carry the asserted commutation to the
original two products. Equality on the pullback cover gives equality on
the test scheme. No quasi-compactness or noetherian condition is needed.

`central_residue_inclusions_baseChange` uses the canonical residue-field
map at a point of the new base. The natural commutative triangle with the
two canonical residue points and the natural comparison of direct and
iterated pullback transport centrality. For a homomorphism,
`central_kernel_fibres_baseChange` additionally uses the actual kernel
base-change isomorphism, before and after taking the residue fibre. Thus
centrality of every actual canonical residue kernel is preserved by every
scheme base change, without reductivity assumptions.

`isCentral_kernel` pulls the reductive groups and homomorphism to the
affine open cover of the arbitrary base. Reductivity, local
quasi-finiteness, flatness and surjectivity persist, as does centrality of
the actual residue kernels. The existing arbitrary-affine theorem gives
centrality on each chart from the retained input. Kernel comparisons and
open-cover locality give centrality of the original actual kernel
inclusion. `centralKernelOfArtinianInput` bundles this unchanged kernel as
a commutative group scheme; its underlying group scheme is definitionally
the original kernel.

`criterion_of_artinianInput` derives the published
`ReductiveFibrewiseCentralIsogenyStatement` with the local input still an
explicit argument. Finite residue kernels give flatness and local
quasi-finiteness of the surjective homomorphism between reductive groups.
The preceding result gives centrality of its kernel. The published
relative-centre theorem and finite-kernel assembly then give finiteness
and the central-isogeny condition. The forward implication is the existing
base-change result.

The provenance is the existing affine centrality reduction, the actual
kernel and iterated-pullback comparisons, open-cover detection of equality,
and the published relative-centre and finite-subgroup assembly theorems.
All schemes and rings range over an arbitrary universe. The open cover may
have an independent index universe. No external structural assertion is
used as an unproved premise beyond the stated local Artinian input.
