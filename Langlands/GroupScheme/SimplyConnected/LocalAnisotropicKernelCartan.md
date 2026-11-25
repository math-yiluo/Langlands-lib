# Cartan obstructions and full-star fixation in the anisotropic kernel

This internal module proves two elementary consequences of
`HasInnerTypeAComponent` and transports them through an actual
`KernelComparison`. Its final local consequences have the explicit premise
`LocalAnisotropicCartanComponentsStatement.{u}`. This module does not prove that
premise.

`HasInnerTypeAComponent.not_three_neighbors` says that a vertex cannot have
three pairwise distinct neighbors with Cartan entry `-1`. Each neighbor
belongs to the named vertex's actual Cartan component. Under the supplied
type-A numbering, a `-1` entry makes the two integer vertex numbers differ
by one. There are at most two such numbers, contradicting injectivity for
three distinct neighbors. The private `typeA_adjacent` lemma unfolds
Mathlib's type-A matrix to obtain this arithmetic adjacency condition.

`KernelComparison.not_three_zero_neighbors` transports this obstruction to
the ambient zero subdiagram. The comparison's vertex equivalence sends each
ambient zero vertex to an actual kernel vertex, preserves distinctness, and
preserves all the Cartan entries used in the argument.

`KernelComparison.star_eq_of_fixed_zero_adjacent` concerns one element of the
full absolute Galois group. Suppose it fixes an ambient zero vertex, and a
second zero vertex has a nonzero Cartan entry with the first. Equivariance
of the actual kernel comparison makes the corresponding kernel vertex
fixed. Thus that Galois element stabilizes its Cartan component.
`HasInnerTypeAComponent` makes its action trivial on every vertex of that
component, including the adjacent vertex. Transporting through the same
comparison fixes the second ambient vertex. This statement permits
permutations of other components.

The local theorems
`not_three_zero_neighbors_of_local_components` and
`star_eq_of_fixed_zero_adjacent_of_local_components` choose the actual
anisotropic-kernel record from `anisotropicKernelIndex` and apply the explicit
local component premise to its index and anisotropy. They do not require the
kernel to be simply connected or absolutely almost simple. All universes and
field and residue characteristics are retained.
