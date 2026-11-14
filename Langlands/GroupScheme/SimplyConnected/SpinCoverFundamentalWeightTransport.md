# Transport of fundamental weights trivial on a kernel

Author: Worker 237.

This internal, derived module constructs the full-kernel comparison
`kernelPostcompIso` for a group-scheme homomorphism postcomposed by a
monomorphism and proves transport rules for the published
`TitsIndexData.FundamentalWeightTrivialOnKernel` predicate. Let `K` be a
field, `G` an affine locally finite type group scheme with actual Tits
index `d`, `v` one of its vertices, and `π : G → H` a group-scheme
morphism. No characteristic restriction is imposed.

The kernel comparison itself is valid over any base scheme. It reuses
`range_kernelι_comp_mono` from [KernelMonomorphism](../KernelMonomorphism.md). On every
test scheme, cancellation of the monomorphism shows that the ranges of
the two actual kernel inclusions agree. Uniqueness of a representing
group scheme then gives the isomorphism
`ker(π ≫ j) ≅ ker(π)`. The theorem `kernelPostcompIso_hom_ι` proves that
this comparison commutes with their inclusions into the source.

For every morphism `j : H → H'`, alignment for `π ≫ j` implies
alignment for `π`: any point killed by `π` is also killed by the
composite. If the underlying relative-scheme morphism of `j` is a
monomorphism, the converse also holds. Indeed, after base change to
`K^s`, cancellation of that monomorphism shows that the composite kills
a point exactly when `π` does. The fundamental-weight character and its
simple-coroot pairings are unchanged.

The Lean proof unfolds the existing alignment predicate, factors the
base-changed composite using functoriality, and uses the identity
preservation of group homomorphisms. The reverse direction uses
preservation of monomorphisms by the scheme pullback functor. This proves
`fundamentalWeightTrivialOnKernel_comp_mono_iff`; the module also supplies
the two directions as methods and specializes preservation to a target
isomorphism and to an identity-component inclusion of a smooth affine
group.

All arguments retain the quantification over every test scheme over
`K^s`. They therefore apply to infinitesimal kernels in characteristic
2. The results do not construct a spin cover or assert the existence of
a fundamental-weight character.

The provenance is internal: these are formal consequences of the
Library predicate, categorical monomorphism cancellation, and
functoriality of the existing group-scheme base change. No classification
or local Kneser–Tits input is used.
