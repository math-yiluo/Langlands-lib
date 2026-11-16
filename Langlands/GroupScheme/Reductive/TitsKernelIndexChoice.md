# Choosing the actual anisotropic kernel and its index

This internal construction packages published representability and
anisotropic-kernel results. It works over every field `k : Type u` for an
affine group scheme locally of finite type with actual `TitsIndexData d`.
Semisimplicity is already part of those index data.

`TitsIndexData.AnisotropicKernelIndex` records an actual representative of the
centralizer of the maximal split torus, its inclusion into the ambient group,
an actual derived subgroup and its inclusion, affineness and local finite
type of that derived subgroup, actual index data on it, its anisotropy, and
the actual `KernelComparison` with the ambient index. The comparison uses the
composite of the derived inclusion and centralizer inclusion. It therefore
retains the actual Cartan and full absolute Galois comparisons of the
published interface.

`nonempty_anisotropicKernelIndex` constructs this record. The proof obtains a
smooth closed centralizer representative from
`torusCentralizer_hasSmoothClosedRepresentative`, obtains its connected
reductivity from `centralizer_isConnectedReductive`, and applies
`derivedSubgroupRepresentability`. The published `titsAnisotropicKernelIndex`
then supplies the derived group's actual index and comparison.
`titsAnisotropicKernel` supplies its anisotropy.
`anisotropicKernelIndex` chooses one such record by classical choice.

No simply connectedness or absolute almost simplicity of this kernel is
asserted. The construction adds no local-field or characteristic assumption
and makes no classification assertion.
