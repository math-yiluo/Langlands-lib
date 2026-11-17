# Joint vector recovery in a prescribed Hilbert realization

This internal prerequisite recovers an algebraic carrier from a dense
inner-product-preserving realization of two commuting actions. The first group
is topological and has compact open subgroups cofinal among open subgroups. Every
algebraic vector is smooth for that action and finite for the second group
action. The source is jointly admissible and carries a positive definite
Hermitian form invariant under both actions.

The target is any complex inner-product space with two unitary actions, and the
supplied dense complex-linear map respects both actions and the given form.
`jointVectorRecovery_of_dense` proves that a target vector is smooth for the
first group and finite for the second precisely when it is in the actual image
of the algebraic carrier. Completeness of the target is not required.

The proof restricts the inner product with the target vector to the source. This
functional is smooth for the first dual action and finite for the second dual
action. Published joint-dual Riesz representation supplies a source vector with
the same functional. Preservation of the inner product and density identify its
image with the original target vector. Conversely, an equivariant map preserves
smooth and finite vectors.

The provenance is internal composition of the published
`UnitaryContragredientCriterion`, antilinear preservation of finite vectors and
dense inner-product separation. Smoothness here means an open stabilizer; it
does not mean differentiability for a real Lie group. This result supplies no
full archimedean group action, differentiable smooth-vector recovery, or
Whittaker uniqueness.

`OperatorUnitaryFormCore.JointVectorRecovery` records this characterization for
the common completion and its two completed actions. The actual
`OperatorJointVectorRecoveryStatement` quantifies every number field in an
arbitrary universe, every natural rank, every actual jointly admissible operator
realization and every supplied full invariant positive form.
`operatorJointVectorRecovery` proves it, without an irreducibility premise.
The target of the characterization is the actual image of the canonical dense
embedding, rather than a replacement representation or a new quotient.

The specialization uses the already proved smoothness of the finite action,
compact finiteness, their commutation and cofinal compact open subgroups of the
finite adelic group. Unitarity and agreement of the completed actions are the
published Hilbert-completion identities. In particular, neither a full
archimedean action nor differentiable smooth-vector recovery is assumed or
concluded. This is an internal prerequisite toward globalization in cuspidal
operator multiplicity one, whose unconditional statement remains open.
