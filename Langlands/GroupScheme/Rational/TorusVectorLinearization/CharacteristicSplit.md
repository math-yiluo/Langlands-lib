# Reduction of torus linearization to positive characteristic

`torusVectorActionLinearization_of_charP` reduces the statement
`TorusVectorActionLinearizationStatement` to positive characteristic, in namespace
`Langlands.GroupScheme.RelativeRoot`.

Its hypothesis `hp` is about one prime `p`. Let `k` be any field with
`CharP k p`. Let `T` be a torus over `k`, `V` a vector group of dimension `n`, and
`a` an action of `T` on `V`. Then `hp` gives coordinates `e` of `V` that satisfy
`IsNaturalVectorCoordinates e` and `IsAffineLinearVectorCoordinates a e`: they are
natural in the test scheme, and the action is scalar linear on affine tests. If
`hp` holds for every prime `p`, the full statement follows for fields of every
characteristic.

## Proof

Fix `k`, `T`, `V`, `n` and `a`. The torus is an affine scheme by
`SplittingAssembly.isAffine_of_isTorus`. Its structure morphism to `Spec k` is
therefore affine, since every morphism between affine schemes is affine. Instance
search derives the `IsAffineHom` instance from this. The published
`IsAffineLinearVectorCoordinates.isLinearVectorCoordinates` needs that instance,
together with naturality, to upgrade scalar linearity on affine tests to scalar
linearity on every scheme test.

`CharP.exists` gives the characteristic `p` of `k`, and
`CharP.char_is_prime_or_zero` splits into two cases.

- If `p` is prime, apply `hp` and upgrade the affine linearity it gives as just
  described.
- If `p = 0`, then `k` has characteristic zero. Every natural coordinate system
  of a vector group, such as the one supplied by `IsVectorGroupOfDimension V n`, is
  then already linear for every action of an affine group scheme. This is the
  published `isLinearVectorCoordinates_of_charZero`.

## Provenance

The case split is internal to this formalization and combines two separate
sources in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015). The
characteristic-zero case is the published theorem
`isLinearVectorCoordinates_of_charZero`. It matches the discussion following
Definition A.1.1, printed p.466 (PDF p.492): over a field of characteristic `0`
the linear structure on a vector group is unique and all homomorphisms are linear.
The positive-characteristic hypothesis `hp` corresponds to Theorem B.4.3, printed
p.577 (PDF p.603). That theorem is stated only for smooth `p`-torsion commutative
groups and contains no characteristic-zero case.
