# Root-annihilator kernels of the actual adjoint torus map

Authors: Worker 1475 and Worker 1334.

For `h : IsAdjointSplitTorusImage q i j p` over an arbitrary field and
universe, this internal unit identifies the integral and real kernels of the
actual torus map `p`. It uses the actual morphisms and the published relative
roots. The real conclusion is
`(RealTorusSpace.cocharacterMapReal p).ker = RealTorusSpace.relativeCentralDirections i`.
No integral-surjectivity, positive-rank, smooth-centre or finite-kernel
hypothesis occurs.

The first theorem shows that an integral cocharacter `ν` is killed by `p`
exactly when `groupHom ν ≫ i` is central on every test scheme. It applies
`IsAdjointSplitTorusImage.comp_eq_one_iff_mem_center` to all points of the
multiplicative group, and uses the published points extensionality theorem
to recover equality of morphisms.

For the integral kernel equality, centrality makes every actual relative
root restrict to zero by `root_restrict_eq_zero_of_isCentral`. Conversely,
the imported unconditional theorem `rootAnnihilatorCentrality` turns
vanishing of the integer pairings with all actual relative roots into
all-test centrality. The connected reductive source supplies all the
smooth, affine and connected hypotheses of that theorem.

The real kernel equality then follows by flat scalar extension from the
integers to the reals. Finiteness of the actual relative roots follows from
`IsSplitTorus.finite_relativeRoots` using the supplied maximal split torus.
`Module.Flat.ker_lTensor_eq` commutes the kernel with extension of scalars,
and `rootAnnihilatorInt_baseChange` identifies the extended integral
annihilator with the published real annihilator. This also covers an empty
root set.

`realKernelEquivCentralDirections` packages the real equality as a linear
equivalence of its two subspaces. Its underlying ambient vector is unchanged,
as stated by `realKernelEquivCentralDirections_coe`.

The provenance is internal composition of the cited Library proofs and
Mathlib's flat base-change theorem. No external-literature result or
additional structural hypothesis is introduced. This unit does not assert
surjectivity of `p` on integral cocharacters or prove the real-surjectivity
conjunct of the full adjoint comparison target.
