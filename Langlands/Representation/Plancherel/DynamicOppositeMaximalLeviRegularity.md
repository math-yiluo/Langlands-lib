# Inverse regularity for the actual maximal-Levi opposite scalar

This derived result specializes the full-unitary inverse regularity problem to
an actual maximal proper dynamic parabolic. It applies over an arbitrary
nonarchimedean local field with independent field and representation-carrier
universes. `IsMaximalProper` says that the represented dynamic parabolic
inclusion is proper and that any factorization through a rational parabolic
has an isomorphism as one of its two factors.

The fixed-embedded-Levi model represents the dynamic parabolic with the
original centralizer as Levi and with its original ambient inclusion. Choose
an actual split component of this Levi. The maximal-Levi cyclic valuation
kernel result gives an adapted product chart with at most one kernel
coordinate. The Levi's original inclusion is the composite supplied by the
fixed-embedded-Levi model.

The domain and irreducibility hypotheses are those for the actual conditional
canonical scalar. Square integrability gives the uniform bound for the inverse
on the common regular unitary locus via `DynamicOppositeInverseBound`.
The product of the two continuation denominators is a nonzero regular function.
Its nonvanishing on the unitary group gives a dense subset of that locus.
Exact ambient twisting fixes the canonical scalar in the actual function
field. Taking inverses establishes fixedness for the inverse in that same
field.

`unitaryRegular_of_ambient_fixed_of_dense_normBound` combines the chart,
fixedness and dense bound. Its rank-zero branch uses a constant fraction. Its
rank-one branch removes the circle poles of a reduced polynomial fraction.
`inverse_regularAt` thus gives algebraic regularity for the original inverse
at each unitary parameter, including those outside the common regular locus.
The maximal-Levi use of a single parameter corresponds to the discussion
following IV.1(13) of Waldspurger's 2003 Plancherel paper, printed p. 283.
