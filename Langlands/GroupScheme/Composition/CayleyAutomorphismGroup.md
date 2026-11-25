# The automorphism group scheme of a Cayley datum

For every Cayley datum `c` over a field `K`, this module constructs
`c.automorphismGroup`, an actual affine group scheme over `Spec K`. It
also constructs a homomorphism `c.automorphismInclusion` into the
Library's `GeneralLinear.groupScheme (Fin 8)`. The theorem
`isAutomorphismRepresentation_automorphismInclusion` proves
`c.IsAutomorphismRepresentation c.automorphismInclusion`. Thus the
inclusion is a closed immersion. On every test scheme `T` over `Spec K`,
nonreduced ones included, its range is exactly the set of invertible
matrices over `Γ(T)` that fix the extended unit and preserve the extended
multiplication. No property of `c` beyond its structure constants and unit
is used. In particular nothing depends on the characteristic or on the
split datum of `SplitCayley`, although the import supplies
`bilinear_apply_eq_sum`.

## Algebraic part

Fix a ring homomorphism `φ : K →+* A` into a commutative ring.

- `multiplicationBilin φ` is `c.multiplicationOver φ` as an `A`-bilinear
  map. Each bilinearity identity reduces to the double sum defining
  `multiplicationOver`.
- `multiplicationDefect φ g` is the bilinear map
  `(x, y) ↦ g(xy) - (gx)(gy)` for a matrix `g`. `unitDefect φ g` is
  `g·1 - 1`, with `1` the extended unit vector.
- `isAutomorphismMatrix_iff`: an invertible `g` satisfies the Library's
  `c.IsAutomorphismMatrix φ g` exactly when all eight coordinates of the
  unit defect vanish and all coordinates of the multiplication defect
  vanish on all pairs of standard basis vectors. The converse direction
  expands an arbitrary pair of vectors by `bilinear_apply_eq_sum`.
- `isAutomorphismMatrix_one`, `IsAutomorphismMatrix.mul` and
  `IsAutomorphismMatrix.inv` show closure under the group operations. For
  the inverse, `g` is injective on `A⁸`, and both equations for `g⁻¹`
  follow by applying `g` to both sides.
- `automorphismSubgroup φ` is the resulting subgroup of `GL₈(A)`.
- `map_unitDefect`, `map_multiplicationOver` and `map_multiplicationDefect`
  show that applying a ring homomorphism `f : A →+* B` to the defects of
  `g` gives the defects of `g.map f` for `f ∘ φ`.

## Scheme part

The construction uses the Library's general cut-out machinery in
`Langlands.GroupScheme.CorepresentedClosedSubgroup`. `GL₈` over `K` is
corepresented by its coordinate ring `𝒪`, with universal matrix `𝔤`.

- `automorphismGenerators` is the set of all coordinates of the unit
  defect of `𝔤`, and of the multiplication defect of `𝔤` on pairs of
  standard basis vectors, computed over `𝒪`. `automorphismIdeal` is the
  ideal they span.
- `classify_unitDefect` and `classify_multiplicationDefect` compute the
  images of these generators under the classifying algebra map
  `classify g : 𝒪 → S` of a matrix `g ∈ GL₈(S)`. They are the
  corresponding defects of `g` itself, by the `map_*` lemmas and the
  published `classify_entry`.
- `mem_automorphismSubgroup_iff_classify`: `g` is an automorphism matrix
  exactly when `classify g` kills `automorphismIdeal`. This is the
  published predicate `Corepresented.IsCutOutBy` for the family
  `automorphismFamily` of subgroups `automorphismSubgroup (algebraMap K A)`,
  recorded as `isCutOutBy_automorphismIdeal`.
- `automorphismGroup` is `Corepresented.cutGroupScheme` of this cut-out
  datum, the spectrum of `𝒪 ⧸ automorphismIdeal`. `automorphismInclusion`
  is `Corepresented.cutHom`.
- `isAutomorphismRepresentation_automorphismInclusion` combines the
  published `Corepresented.isClosedSubgroup_cutHom` with
  `Corepresented.range_cutHom` and `Corepresented.mem_cutSubgroupFunctor`.
  The latter identify the range on every test scheme `T` with the
  automorphism equations for the matrix
  `GeneralLinear.pointsEquiv (Fin 8) K T g` over the algebra of global
  sections of `T`. This is exactly the second clause of
  `IsAutomorphismRepresentation`.
- The instances `isAffineHom_automorphismGroup` and
  `locallyOfFiniteType_automorphismGroup` give the structure morphism
  these properties. It is the closed immersion followed by the structure
  morphism of `GL₈`. That morphism is affine by the published
  `GeneralLinear.isAffineHom_groupScheme`. It is of finite type because
  the coordinate ring of `GL₈` is smooth over `K`, by the published
  `coordinateRing_smooth`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
treats the automorphism group scheme `Aut_alg(C)` of a Cayley algebra `C`
as the functor of unit-preserving algebra automorphisms of `C ⊗ R` over
commutative `F`-algebras `R`. See Theorem 25.14, printed p.360 / PDF
p.383, for the split case, and Theorem 26.19, printed p.373 / PDF p.396,
in general. Representing this functor by an explicit ideal in the
coordinate ring of `GL₈` is a derived construction. The module proves no
structural property of the group (smoothness, connectedness, type `G₂`).

`CayleyDatum.multiplicationBilin` is the bilinear multiplication from `CayleyGradingTorus`.
