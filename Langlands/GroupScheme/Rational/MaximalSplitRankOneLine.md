# Equivariant lines through rational points of nonmultipliable root subgroups

This internal derived support module, in namespace
`Langlands.GroupScheme.MaximalSplitSubgroup`, is the first rank-one step of the
proof of `MaximalSplitSubgroupStatement` (Borel–Tits 1965, Theorem 7.2). In
that proof the root groups of the split subgroup are additive lines inside the
relative root subgroups `U_(a)` of the nonmultipliable relative roots `a`. This
module builds such a line through any prescribed nontrivial rational point.

Throughout, `k` is a field and `Ga` is the one-dimensional vector group
`VectorGroup.groupScheme (CommRingCat.of k) 1`. `scalarPoint _ Z c` is the
`Z`-point of `Ga` with coordinate `c`.

## Lines in vector coordinates (section `Line`)

Fix a group scheme `U` over `Spec k` and natural vector coordinates
`e : (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X, ⊤))`
(`RelativeRoot.IsNaturalVectorCoordinates e`, hypothesis `he`). The Library
isomorphism `RelativeRoot.vectorGroupIso e he` identifies `U` with the
standard vector group of dimension `n`.

- `lineMatrix v`: the `n × 1` column matrix with entries `v : Fin n → k`.
- `lineHom e he v : Ga ⟶ U`: the homomorphism `c ↦ c • v` in the coordinates
  `e`. It is the matrix homomorphism `matrixHom (lineMatrix v)` followed by the
  inverse of `vectorGroupIso e he`.
- `lineHom_coordinates`: on every test `Z` and every point `x` of `Ga`, the
  `e`-coordinates of `x` followed by `lineHom e he v` are
  `r ↦ v r · (coordinate of x)`. Here `v r` maps into `Γ(Z, ⊤)` by
  `scalarMap`.
- `lineHom_scalarPoint`: the special case `x = scalarPoint _ Z c`, with
  coordinates `r ↦ v r · c`.
- `mono_lineHom`: if `v ≠ 0`, the underlying morphism of schemes of
  `lineHom e he v` is a monomorphism.
- `pointVector e x : Fin n → k`: the coordinates of a rational point `x` of
  `U`, transported to `k` along `Γ(Spec k, ⊤) ≅ k`.
- `scalarMap_base`: on the base test `Over.mk (𝟙 (Spec k))`, `scalarMap`
  inverts the identification `Γ(Spec k, ⊤) ≅ k`.
- `lineHom_pointVector_one`: the line with direction `pointVector e x` takes
  the value `x` at the parameter `1`.
- `pointVector_ne_zero`: if `x ≠ 1`, then `pointVector e x ≠ 0`.

## Torus equivariance (section `Equivariant`)

Let `i : S ⟶ G` with `S` commutative, let `a` be a character of `S`, and let
`j : U ⟶ G` represent the relative root subgroup functor
`RelativeRoot.subgroup i a` (hypothesis `hj`). Suppose the coordinates `e` are
weight-vector coordinates of weight `a` for the conjugation action
`RelativeRoot.subgroupAction i a j hj` of `S` on `U`
(`RelativeRoot.IsWeightVectorCoordinates`, hypothesis `hw`).

- `subgroupAction_lineHom`: a torus point `t` acts on
  `scalarPoint _ Z c ≫ lineHom` as the line at the parameter `a(t) · c`, where
  `a(t) = charValue a Z t`.
- `isTorusEquivariant_lineHom`: `lineHom e hw.1 v ≫ j` is torus-equivariant of
  weight `a` in the sense of `VectorGroup.IsTorusEquivariant`, that is,
  `i(t) x(c) i(t)⁻¹ = x(a(t) c)` on every test.

## Lines through root points (section `RootLine`)

Now `G` is smooth and affine over `k`.

- `exists_line_through_rootPoint`: let `S` be a split torus (`hT`),
  `i : S ⟶ G`, `a ≠ 0` a character with no higher multiples among the relative
  roots (`RelativeRoot.HasNoHigherRoots i a`: `m • a` is not a relative root
  for `m ≥ 2`), and `j` a representative of `RelativeRoot.subgroup i a`. Let
  `u` be a rational point of `RelativeRoot.subgroup i a` with `u ≠ 1`. Then
  there is `x : Ga ⟶ G` such that
  1. `x` is torus-equivariant of weight `a`,
  2. the underlying morphism of schemes of `x` is a monomorphism,
  3. `SubgroupFunctor.range x ≤ RelativeRoot.subgroup i a`, and
  4. `x` takes the value `u` at the parameter `1`.

## Proofs

`lineHom_coordinates` rewrites the coordinates through the Library identity
`RelativeRoot.coordinates_comp_vectorGroupIso_hom`. The inverse and forward
isomorphisms cancel, and the result is the coordinate formula
`VectorGroup.coordinates_matrixHom` for matrix homomorphisms. `mono_lineHom`
compares a nonzero coordinate `r` of two points with the same image. The two
coordinates differ by the factor `v r`, which is a unit because it is the image
of a nonzero field element. `lineHom_pointVector_one` and `pointVector_ne_zero`
compare coordinates using the injectivity of `e` and of `toAdd`.

`subgroupAction_lineHom` uses the weight-vector identity `hw.2`: the action
multiplies every coordinate by `a(t)`. `isTorusEquivariant_lineHom` composes
this with `j` and uses `RelativeRoot.subgroupAction_act_comp`, which says that
the action followed by `j` is conjugation by `t ≫ i` in `G`.

`exists_line_through_rootPoint` takes weight-vector coordinates of weight `a`
on `U` from the Library theorem
`RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots`. Since `j`
represents the root subgroup, `u = u' ≫ j` for a rational point `u' ≠ 1` of
`U`. The line is `lineHom e hw.1 (pointVector e u') ≫ j`. It is equivariant by
`isTorusEquivariant_lineHom`. It is a monomorphism because `mono_lineHom`
applies (by `pointVector_ne_zero`) and `j` is a monomorphism. Its range lies in
the range of `j`, which is the root subgroup. Its value at `1` is `u` by
`lineHom_pointVector_one`.

## Provenance

The use of one-parameter additive subgroups through root points is the setting
of Borel–Tits 1965, §7.2 (pp. 64–68). The construction here is derived: it
takes the vector-group structure of the nonmultipliable root subgroup from the
Library and uses only linear algebra in its coordinates. No statement is
assumed.
