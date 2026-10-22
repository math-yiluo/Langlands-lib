# Upper triangular matrices inside standard block parabolics

Author: Worker 6.

This module constructs the actual upper triangular subgroup of
`Langlands.GeneralLinear n R` and its inclusion into every published standard
block parabolic. It works for every commutative ring `R`, in an arbitrary
universe, every natural rank `n` (including zero), and every existing
`BlockShape n`. No field, topology, or matrix factorization is assumed.

## Constructions and meaning

`upperTriangularSubgroup n R` is the subgroup of invertible matrices whose
strictly lower entries vanish. Its carrier uses Mathlib's
`Matrix.IsUpperTriangular`, and `mem_upperTriangularSubgroup_iff` states the
explicit criterion `j < i → g i j = 0`. Closure under multiplication and
inversion follows from Mathlib's block triangular matrix results.

`BlockShape.upperTriangularInParabolic B R` is an injective group homomorphism
from that subgroup to `B.parabolic R`. It preserves the underlying matrix
exactly, as stated by `upperTriangularInParabolic_val`; the injectivity theorem
uses equality of those underlying matrices. This is the subgroup inclusion,
not a choice of another representative.

## Implemented argument

`index_lt_index_of_block_lt` proves that every coordinate of an earlier block
precedes every coordinate of a later block. The published consecutive-block
numbering expands as the sum of preceding block sizes plus the within-block
coordinate. Inclusion of the initial finite index sets bounds the sum through
the earlier block by the sum before the later block. The earlier within-block
coordinate is strictly smaller than its block size, giving the strict ordering.

`mem_parabolic_of_isUpperTriangular` applies that ordering to the published
entrywise parabolic criterion `BlockShape.mem_parabolic_iff`. The resulting
subgroup containment defines the homomorphism through `Subgroup.inclusion`.
The membership theorem keeps its existing name and statement from
`Representation/Parabolic/QuotientCompactProof`; it is located here so both the
algebraic inclusion and the compactness proof can import it. The shared ordering
lemma also serves `Representation/Geometric/WeylUniquenessProof`.

## Provenance and scope

These are internal constructions and algebraic deductions from the published
`Basic` and `Blocks` definitions and Mathlib's matrix and finite-sum APIs. No
external theorem or literature statement is newly formalized here. The module
supplies the inclusion needed to pass from a general-field upper triangular
Bruhat factorization to parabolic double-coset representatives. It does not
prove that factorization, representative existence, minimality, or uniqueness.
