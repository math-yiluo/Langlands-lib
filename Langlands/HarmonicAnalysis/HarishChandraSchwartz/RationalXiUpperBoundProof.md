# Waldspurger's upper bound for the actual Xi

`Langlands.HarishChandraSchwartz.rationalXiUpperBound` proves
`RationalXiUpperBoundStatement.{u}` at an arbitrary universe `u`. On the weak
split-component chamber, it bounds the actual spherical function using the
minimal modulus and matrix height. The degree is fixed before choosing the
left and right translates. [Target statement and source](RationalXiUpperBoundStatement.md)

The proof applies `rationalXiUpperBound_of_jacquetUnipotent` to
`rationalMinimalInducedJacquetUnipotent`. The latter supplies uniform
nilpotence of the central operators minus the identity on the normalized
Jacquet modules of the actual minimal induction. The reduction combines
Casselman asymptotics on the finitely many faces, polynomial coefficient
bounds on their lattices, and the spherical coefficient identity.
[Jacquet unipotence proof](RationalMinimalInducedJacquetProof.md) and
[Xi reduction](RationalXiUpperBoundReduction.md)
