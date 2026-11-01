# Supported cut diagrams and their homogeneous quotients

This internal algebraic module starts with the existing signed cut diagram.
A subdiagram assigns a submodule to each coordinate and proves that every
actual diagram transition preserves it. Coordinate membership defines the
total and homogeneous support submodules. Each signed insertion preserves
total support because transitions preserve support and support is closed under
scalar multiplication. Finite summation, extension by zero and restriction
give preservation by the total and homogeneous differentials.

The module restricts those same differentials to the support submodules. For
two subdiagrams, each coordinate quotient is the upper submodule modulo the
pullback of the lower one. The actual restricted transitions descend to these
quotients and satisfy the diagram laws on representatives. No assumption that
the lower subdiagram lies in the upper one is needed for these pullbacks.

Coordinate quotient projections commute with extension, restriction, signed
insertion and both differentials. The original insertion signs remain in
every square. The homogeneous projection is surjective by choosing an upper
representative in each coordinate. Its kernel is exactly the pullback of the
lower homogeneous support. The first isomorphism theorem therefore gives
`degreeQuotientEquiv`, from the quotient of the actual homogeneous supports to
the homogeneous product of the coordinate quotients. Its formula on
representatives is the coordinate quotient projection.

Finally the actual homogeneous differential descends to those actual support
quotients, and `degreeQuotientEquiv_differential` proves the commuting square
with the signed differential of the coordinate quotient diagram. The proof
reduces a quotient class to a representative and applies the previously
proved projection square.

The provenance is internal linear algebra, using the already defined cut
diagram and elementary submodule quotients. The coefficient modules and the
linearly ordered cut index retain independent universes. Only the
differential results require a finite cut index. This module proves no
geometric identification, filtration exhaustion, or exactness.
