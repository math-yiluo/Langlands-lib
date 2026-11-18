# Actual fundamental highest weights for the split norm-one representation

This internal construction transports the standard column
representation's actual highest weight through the prescribed actual
norm-one splitting isomorphism.

The general transport theorem accepts any supplied actual split pinning
of the special-linear target and an actual highest-weight proof for its
column representation. It uses the constructed pinning on the norm-one
group, whose torus, integral root datum, base and fundamental weights
are retained and whose inclusion is composed with the inverse
splitting isomorphism. The transported representation is definitionally
the original chart representation in `NormOneMatrixRepresentation`.

The existence theorems have no supplied highest-weight premise. For
matrix dimension at least two, write the dimension as `n+2` and use
`specialLinearFirstFundamentalHighestWeight`, which gives the actual
diagonal torus with adjacent-root numbering and the standard
representation's first fundamental highest weight. Transport through
the actual splitting chart then gives a fundamental highest weight of
the norm-one representation. The arbitrary-chart theorem retains the
special-linear pinning witness and both highest-weight proofs.

The Prop-valued `NormOneFundamentalHighestWeightStatement` and its
proved instance specialize this construction to the unconditional
finite Galois splitting chart of every central simple algebra `A`.
Their scope is every `k, A : Type u`, for every `u`, in every
characteristic. The numerical hypothesis that the reduced degree is at
least two ensures that there is a fundamental-weight vertex; a
degree-one norm-one group has no such vertex.

Provenance is internal: this is a deduction from the actual standard
highest-weight construction and actual pinning/representation
transport, with the unconditional splitting chart. The general Tits
algebra comparison and Brauer-class normalization remain separate
obligations.
