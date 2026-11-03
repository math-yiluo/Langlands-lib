# Uniqueness of the scalar structure of weight vector coordinates

This module proves the uniqueness half of the published predicate
`HasUniqueWeightVectorStructure b χ` from `Rational.WeightSemigroupStatement`,
and builds the full predicate from one system of coordinates. Throughout, `k` is
a field, `S` a commutative group scheme over `Spec k`, `V` a group scheme over
`Spec k` with an automorphic action `b` of `S`, and `χ` a character of `S`.
Vector coordinates `e` identify the `T`-points of `V` with `Γ(T, ⊤)ⁿ`, as in the
published predicates `IsNaturalVectorCoordinates` and
`IsWeightVectorCoordinates`.

## Statements

`coordinateSmul e T c v` is the `T`-point whose `e`-coordinates are `c` times
those of `v`; `coordinateSmul_coord` records this. It is the expression compared
in the uniqueness clause of `HasUniqueWeightVectorStructure`.

For natural coordinates `e`:

- `IsNaturalVectorCoordinates.comp_coordinateSmul`: restricting `c · v` along
  `f : W ⟶ T` gives the restriction of `c` times the restriction of `v`.
- `IsNaturalVectorCoordinates.cancel`: if `f : W ⟶ T` is injective on global
  functions, then `f ≫ x = f ≫ y` implies `x = y` for `T`-points of `V`.

For weight vector coordinates of weight `χ`,
`IsWeightVectorCoordinates.coordinateSmul_eq_act` states that scaling by the
unit `χ(s)` is the action of the torus point `s`. This is a restatement of the
second clause of `IsWeightVectorCoordinates`.

Two lemmas about an actual split torus `S` (`IsSplitTorus S.toGrp`) are placed
in namespace `Langlands.GroupScheme`, so dot notation applies:

- `IsSplitTorus.exists_pairing_eq_pos`: a nonzero character `χ` has
  `⟨χ, ζ⟩ = D` for some cocharacter `ζ` and some natural number `D > 0`. This
  is the one-vector case of the published `IsSplitTorus.exists_scaled_pairings`.
- `IsSplitTorus.nsmul_ne_zero`: if `a ≠ 0` and `r ≠ 0` then `r • a ≠ 0`. This
  uses the published injectivity of `χ ↦ 1 ⊗ χ` into the rational character
  space.

The main results assume `IsSplitTorus S.toGrp` and `χ ≠ 0`:

- `coordinateSmul_eq_of_isWeightVectorCoordinates`: for any two systems `e`, `e'`
  of weight vector coordinates of weight `χ`, possibly with different numbers of
  coordinates, `coordinateSmul e T c v = coordinateSmul e' T c v` for every test
  scheme `T`, scalar `c` and point `v`.
- `hasUniqueWeightVectorStructure_of_coordinates`: one system `e` of weight
  vector coordinates of weight `χ` gives `HasUniqueWeightVectorStructure b χ`.

The module does not prove that such coordinates exist. No additivity of
`coordinateSmul` is used or proved, and `V` need not be commutative.

## Auxiliary test schemes

The namespace `WeightVectorUniqueness` contains the test schemes used in the
proof. Each is an `Over (Spec k)` object built with `Spec.map` of a `k`-algebra
structure map.

- `UniversalRing k n = k[y][x₁, …, xₙ]` with `universalScheme k n`,
  `universalCoord k n` (the images of the `xⱼ`) and `universalScalar k n`
  (the image of `y`).
- `structureRingHom T : k →+* Γ(T, ⊤)` is the structure map of `T`.
  `classifyingRingHom T c z` sends `y ↦ c` and `xⱼ ↦ zⱼ`. `classifyingMap T c z`
  is the corresponding morphism `T ⟶ universalScheme k n` over `Spec k`. It
  pulls back `y` to `c` (`classifyingMap_universalScalar`) and `xⱼ` to `zⱼ`
  (`classifyingMap_universalCoord`).
- `universalPoint e` is the point of `V` over the universal scheme with
  coordinates `(x₁, …, xₙ)`. `classifyingMap_universalPoint` shows that the
  classifying map of `v`'s coordinates pulls it back to `v`.
- `LaurentRing k n = k[t, t⁻¹][x₁, …, xₙ]` with `laurentScheme k n`.
  `powerRingHom D` sends `y ↦ t ^ D` and `xⱼ ↦ xⱼ`. It is injective for `D > 0`
  (`powerRingHom_injective`: it is `expand D` followed by the inclusion of
  polynomials into Laurent polynomials). `powerMap D` is the corresponding
  morphism of test schemes, and `powerMap_appTop_injective` shows it is
  injective on global functions.
- `laurentTorusPoint ζ` is the point `ζ(t)` of `S` over the Laurent scheme.
  `pointsEquiv_laurentTorusPoint` shows that `χ(ζ(t)) = t ^ D` when
  `⟨χ, ζ⟩ = D`.

## Proof

Let `e` and `e'` be weight vector coordinates of weight `χ`. Choose a
cocharacter `ζ` with `⟨χ, ζ⟩ = D > 0`.

1. Universal case (`coordinateSmul_universalScalar_eq`). Let `v` be a point of
   `V` over the universal scheme. Pull back `y · v` along `powerMap D`. By
   naturality the result is `t ^ D` times the pulled-back point, in either
   coordinate system (`IsWeightVectorCoordinates.powerMap_coordinateSmul`).
   Since `t ^ D = χ(ζ(t))`, this equals `b.act (laurentTorusPoint ζ)` applied to
   the pulled-back point, and that expression does not mention `e` or `e'`.
   The two scaled points therefore agree after pullback along `powerMap D`.
   `powerMap D` is injective on global functions and `e` is natural, so they
   agree on the universal scheme (`IsNaturalVectorCoordinates.cancel`).
2. General case. Given `T`, `c` and `v`, the classifying map `g` of
   `(c, e-coordinates of v)` satisfies `g*(y) = c` and `g ≫ universalPoint e = v`.
   Naturality of both coordinate systems reduces `c · v` to the pullback along
   `g` of `y · universalPoint e`, where step 1 applies.

The first conjunct of `HasUniqueWeightVectorStructure` is the given system `e`;
the second is `coordinateSmul_eq_of_isWeightVectorCoordinates`.

## Provenance

This is a derived contribution. Conrad–Gabber–Prasad, *Pseudo-reductive
Groups* (2nd ed.), Lemma 3.3.8 (printed pp. 111–112), states that the
successive quotients of the cyclic-tail filtration are vector groups with a
unique `S`-equivariant linear structure. Its proof derives uniqueness from
the uniqueness of the `S`-weight on `Lie(V_j)`, "exactly as in the proof of
Lemma 2.3.8". The Lean proof above uses a different route,
which we found for this formalization: the universal test scheme
`Spec k[y][x]` and its injective pullback along `y ↦ t ^ D` to
`Spec k[t, t⁻¹][x]`. Here the scalar `t ^ D` is the torus action of `ζ(t)`.
The uniqueness statement proved is that of the published
`HasUniqueWeightVectorStructure` predicate, which compares the scalar
multiplications of any two systems of weight `χ` vector coordinates.
