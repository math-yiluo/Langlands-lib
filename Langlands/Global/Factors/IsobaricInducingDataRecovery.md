# Recovering cuspidal data from common local embeddings

The exceptional set in the inducing-data rigidity hypothesis is the union of
the given exceptional set and those of the finitely many spectral
presentations. Their unramified data give nonzero spherical fixed spaces
outside the union. The lemma `isSpherical_of_isIsobaricSum` proves that
the first sum is spherical. The lemma `IsIsobaricSum.isSubquotient_normalizedProduct`
gives the subquotient witnesses in the two normalized block inductions.
These are the local steps of Getz–Hahn (2024), Theorems 10.6.3 and 10.6.4,
pp. 285–286 (one-based PDF pp. 297–298).

The common embedding hypothesis gives an intermediate local object. In each
global subquotient the corresponding isobaric sum and the common object
are equivalent by `OperatorSubquotient.nonempty_local_equiv_of_injective`.
The composed equivalence transports the second subquotient witness to the
first sum by postcomposing its surjective intertwiner. The first sum thus
gives the common spherical subquotient used in
`CuspidalInducingDataRigidityStatement`, the Library form of Getz–Hahn
Theorem 10.7.2, p. 287 (one-based PDF p. 299).

The lemma takes inducing-data rigidity as a premise and recovers the
bijection and the equalities of positive-rank cuspidal classes from the
finite-place part of the strong multiplicity-one hypotheses.
