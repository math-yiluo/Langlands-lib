# The unimodular involution on actual Hecke functions and corners

Author: Worker 143.

This internal construction supplies the involution needed for the
character-limit proof in Task 5667. On the existing Schwartz–Bruhat test
functions it is the conjugate-linear equivalence
`TestFunction.adjoint f (x) = conj (f (x⁻¹))`. Local constancy and compact
support follow by composition with inversion and conjugation.

`adjoint_mem_biInvariant` interchanges left and right invariance.
`adjoint_convolution` reverses the actual convolution product when the
measure is finite on compact sets, right invariant and inversion invariant.
Its proof uses the published measure-preserving anti-homeomorphism pullback
identity at inversion and then conjugates the scalar integral.

The module installs this operation as `Star` on the existing measure-indexed
`HeckeAlgebra μ`, with involutivity and compatibility with complex scalars.
When the measure is also left invariant, these hypotheses give `StarRing`.
It also restricts the same operation to every actual compact-open corner
`HeckeAlgebra.Corner μ K hK`. The normalized subgroup indicator is fixed by
the involution, and the corner embedding preserves it.

All the mathematical content is derived from the existing test-function,
convolution and corner constructions. The measure conditions are explicit:
this formula is the unimodular involution, and this module does not assert
that it reverses convolution for a general Haar measure.
