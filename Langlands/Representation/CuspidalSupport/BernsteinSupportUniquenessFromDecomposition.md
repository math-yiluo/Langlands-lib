# Inertial-support uniqueness from Bernstein decomposition

This internal reduction derives uniqueness of the Library's actual inertial
support relation from Bernstein decomposition. It imports the existing
off-diagonal Hom reduction from `BernsteinInductionRestrictionAssembly` and
supplies its premise using the decomposition statement. It supports the proof
of Renard VI.10.6, Proposition (i), when Bernstein decomposition (Renard VI.7.2)
is already an input. It supplies no unconditional proof of either source theorem.

Fix a nonarchimedean local field, the standard reductive-group data, a
`BernsteinStandardFamily`, and independent field and carrier universes `uF`
and `uV`, as in `BernsteinSupportComparison`.

`bernsteinInertialSupportUniqueness_of_bernsteinDecomposition` takes
`BernsteinDecompositionStatement.{uF,max uF uV}` as an explicit premise.
It applies the imported
`bernsteinInertialSupportUniqueness_of_offDiagonalHomsZero` to the second
clause of this premise for the specified family. The conclusion is exactly
`BernsteinInertialSupportUniquenessStatement.{uF,uV}`. The coproduct clause
is not needed.

The imported lemma uses actual support witnesses to put the same irreducible
representation in both full blocks. Subquotient transitivity gives membership
in each saturated block, and `bernsteinBlockProperty_iff_saturated` gives the
full block properties needed by the Hom condition. If the indices differ,
orthogonality makes the identity zero, so the representation is a categorical
zero object. Its irreducibility contradicts this, giving equality of the two
indices. This module reuses that proof without redeclaring its helper.

`bernsteinInertialSupportUniquenessFromDecomposition` is a defined proof term
delegating to this wrapper, with the same premise and conclusion. It provides
the reduction as an infrastructure definition without adding a new object
property or any additional hypothesis.

The universe in this premise matters: support witnesses and their inductions
have carriers in `max uF uV`. A hypothesis giving Bernstein decomposition only
for carriers in `uV` cannot in general supply this saturated instance. A
published proof polymorphic in both universes can be instantiated at the
required common universe.

The provenance is internal: the proof composes the published orthogonality
reduction with the Hom condition already present in the Bernstein decomposition
statement. The reduction itself uses the actual induction-subquotient definition
of support. The wrapper introduces no association, admissibility, finite-length,
or additional representation-theoretic premise.
