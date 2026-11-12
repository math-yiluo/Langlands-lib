# Action kernels in finite representation filtrations

Author: Worker 154. Module `Langlands.Representation.Intertwining.PQFilteredKernels`,
namespace `Langlands.PQFilteredKernels`.

`gradedKernel s X φ` constructs the intersection of the actual group-algebra
action kernels on all grades of a finite representation-functor filtration
`s`, evaluated at an object `X` and restricted along a homomorphism
`φ : B → H` from a commutative group. The module proves equality of its
radical with that of the ambient action kernel, and the resulting criterion
for comaximality against any ideal.

## Source and scope

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, VII.3.3, proof of the Lemma,
printed p.234 / PDF p.240. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read this page. The provenance is derived: the module isolates
an algebraic consequence of an actual supplied filtration, without asserting
existence of the geometric-lemma support filtration needed by the original
application.

The hypotheses are an arbitrary group `H`, a commutative group `B`, any source
category and functor `F` to complex representations of `H`, an actual finite
filtration `s` of length `n`, an object `X`, and a homomorphism `φ : B → H`.
All carrier and category universes remain independent. No topology,
central-image condition, finite-dimensionality, finite length or
semisimplicity is used.

## Implemented argument

The private helper `map_action` extends equivariance linearly to the group
algebra by induction on its zero, sum and single-element constructors.
`kernel_le_gradedKernel` applies this compatibility to each upper-step
inclusion and quotient projection: an element killing the ambient object
kills each upper step and every graded quotient.

`action_mem_previous` proves the converse one-step assertion: an element in
`gradedKernel` maps step `i+1` into step `i`. It applies the actual quotient
projection, uses the zero action on that grade, and reads vanishing of the
quotient class as membership in the preceding submodule. `pow_mem_kernel`
then inducts on the filtration index. For every vector in step `j`, the
`j`-th power of the action is zero. At the full step this says that the
`n`-th power of the group-algebra element belongs to the ambient kernel,
including the empty-filtration case.

Consequently `radical_kernel_eq` proves that the ambient and graded kernels
have the same radical. `sup_kernel_eq_top_iff` proves, for every ideal `I`,
that `I + ambientKernel` is the whole group algebra if and only if
`I + gradedKernel` is the whole algebra. The reverse implication sends the
latter sum into the radical of the former and uses that an ideal whose
radical is the whole ring is itself the whole ring.

## Retained application obligations

For VII.3.3(i) ⇔ (ii), one must still supply a finite filtration of the
quotient by the identity boundary support image and identify its actual
grades with the specified geometric-lemma pieces, with the same action of
`A_M`. This module does not construct those identifications or prove the
exponent-disjointness clauses of `PQRegularityLemmaStatement`. It is an
auxiliary construction for Task 5300, not the exact regularity-lemma proof.

The sole import is the unchanged
`Langlands.Representation.Intertwining.PQRegularity`, which supplies
`groupAlgebraKernel` and the actual representation-filtration interface.
