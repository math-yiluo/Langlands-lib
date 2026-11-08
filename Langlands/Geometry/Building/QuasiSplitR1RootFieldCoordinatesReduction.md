# Type R1 root field coordinates from the structural statements

This internal unit reduces the published
`QuasiSplitR1RootFieldCoordinatesStatement.{u}` to four published structural
statements, none of which is proved in the Library:

- `QuasiSplitTorusCentralizerExistenceStatement.{u}`: some maximal split torus
  of a quasi-split group has a centralizer represented by a closed torus.
- `MaximalSplitTorusConjugacyStatement.{u}`: maximal split tori of a connected
  reductive group are conjugate by rational points.
- `RootDatumExistenceStatement.{u}`: a split maximal torus of a connected
  reductive group has a reduced root datum.
- `RelativeRootSystemStatement.{u}`: the relative roots of a maximal split
  torus form a root system, possibly nonreduced.

The reduction keeps the published statement's generality: every field, every
universe and every characteristic. Coordinates, characters and valuations are
not supplied.

## The centralizer is a torus

`isTorus_of_quasiSplit_torusCentralizer` states that, under the first two
statements, every representative `j : Z -> G` of the centralizer of a maximal
split torus `i` of a quasi-split group is a torus. The proof follows the
published `quasiSplitMaximalTorusCentralizer_of_exists_torusCentralizer`.
Conjugacy moves the given closed torus representative to a representative of
the centralizer of `i`, by the published `torusCentralizer_of_iso_square`. The
canonical isomorphism `isoOfIsRepresentedBy` between two representatives of
the same subgroup functor then transfers `IsTorus` to `Z`, by
`IsTorus.of_iso`.

## The reduction

`quasiSplitR1RootFieldCoordinates_of_structuralStatements` proves the R1
statement from the four statements. Take the data of the R1 statement: a
quasi-split `G`, a maximal split torus `i : S -> G`, a representative
`j : Z -> G` of its centralizer, `s` with `s ≫ j = i`, and an indivisible
relative root `a` with `2a` not a root. The proof applies the published
`rootFieldCoordinatesOfTorus` to `Z` itself, made a commutative group scheme
by `IsTorus.isCommMonObj`, with `f` the homomorphism `s`. Its hypotheses are
obtained as follows.

- `G` is connected reductive and smooth, hence locally of finite type, by
  quasi-splitness.
- `j` is closed by the published `IsSplitTorus.isClosedSubgroup_torusCentralizer`.
  Hence `Z` is affine and locally of finite type.
- The centralizer of `Z` is its range. The centralizer of `Z` lies in the
  centralizer of `S`, which is the range of `j`, by
  `torusCentralizer_le_of_factor`. The range of the commutative `Z` lies in its
  own centralizer, by `range_le_torusCentralizer`. So `j` is a maximal torus by
  `isMaximalTorus_of_torusCentralizer_eq`, and its base change to every field
  is a maximal torus by `isMaximalTorus_baseChange_of_torusCentralizer_eq`.
- The proved `torusFiniteGaloisSplitting` gives a finite Galois extension
  `K/k` splitting `Z`.
- Root datum existence over `K` gives a root datum of the base change of `j`,
  using `IsConnectedReductive.baseChange_of_algebraicExtension`.
- The relative root system and `2a` not a root give `HasNoHigherRoots i a`, by
  `HasRelativeRootSystem.eq_one_of_nsmul_mem_of_two_not_mem`.

`rootFieldCoordinatesOfStructuralStatements` is the coordinate structure
chosen from this nonempty type, for the same data and the same four premises.

## Scope

All four structural statements remain explicit premises. The unit does not
prove the R1 statement unconditionally, the R2 statement, or apartment
existence.
