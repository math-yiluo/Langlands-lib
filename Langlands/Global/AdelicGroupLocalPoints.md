# Actual adelic group points at every place

This module relates the actual adelic point group
`AdelicGroupPoints F G = G.affinePoints (CommAlgCat.of F (AdeleRing (𝓞 F) F))`
of a group scheme `G` over a number field `F` to its points over the
completions of `F`. It is derived infrastructure for the local-to-global
adelic Iwasawa argument. It proves no local Iwasawa decomposition, constructs no
compact subgroup, and does not prove `AdelicGroupPoints.ParabolicIwasawaStatement`.

## Places, completions and local point groups

`Place F` is the sum type `InfinitePlace F ⊕ FinitePlace F`: archimedean places
on the left, finite places on the right. `placeCompletion F i` is the actual
completion as an `F`-algebra: `w.Completion` at an archimedean place `w` and
`FiniteCompletion F v = v.adicCompletion F` at a finite place `v`. It carries the
existing topology, topological-ring and Hausdorff instances of those
completions.

`adeleProjection F i` is the `F`-algebra coordinate projection from the actual
adele ring to `placeCompletion F i`: the `w`-component of the infinite part, or
the `v`-component of the finite restricted-product part. Each projection is
continuous (`continuous_adeleProjection`).

`PlaceGroupPoints F G i` is `G.affinePoints (placeCompletion F i)` with the
Library's regular-function evaluation topology
`G.affinePointsTopologicalSpace`; for affine `G` it is a Hausdorff topological
group. `FinitePlaceGroupPoints F G v` is the same carrier written literally over
`FiniteCompletion F v`, with the same evaluation topology.

## Projections

`AdelicGroupPoints.atPlace F G i` is the continuous group homomorphism induced
on points by `adeleProjection F i`. `atFinitePlace` and `atInfinitePlace` are its
restrictions to finite and archimedean places, with the Library's
`InfinitePlaceGroupPoints` carrier at archimedean places. The evaluation lemmas
`atPlace_evaluation`, `atFinitePlace_evaluation` and
`atInfinitePlace_evaluation` say that evaluating the local point at a regular
function is the corresponding coordinate of the adelic evaluation.

- `ext_atPlace`: for affine `G`, two adelic points with the same local point at
  every place are equal.
- `eventually_atPlace_evaluation_mem`: for every regular function `a`, the value
  of the local point of an adelic point at `a` lies in the valuation ring
  `v.adicCompletionIntegers F` at all but finitely many finite places `v`.
- `atPlace_map`: for a group-scheme homomorphism `f : G ⟶ H`, the local point
  of `map F G H f x` is the image of the local point of `x` under the point map
  `G.affinePointsTarget f` over the completion.
- `eventually_place_of_finite`: a property of places holding at all but finitely
  many finite places holds at all but finitely many places, since there are only
  finitely many archimedean places.

## Gluing local points

Assume `G.X.left` is affine. A family `x i` of local points is an adelic family
(`IsAdelicFamily`) if, for every regular function `a`, its value at `a` lies in
`v.adicCompletionIntegers F` at all but finitely many finite places. The
`F`-algebra homomorphisms from the coordinate ring corresponding to such a
family assemble (`glueAlgHom`) into one `F`-algebra homomorphism to the adele
ring, and `glue F G x hx` is the corresponding adelic point.

- `glue_evaluation`: each adele coordinate of a value of `glue F G x hx` is the
  value of `x i`.
- `atPlace_glue`: the local point of `glue F G x hx` at `i` is `x i`.
- `isAdelicFamily_of_eventually_eq`: a family equal to the local points of one
  adelic point at all but finitely many finite places is an adelic family.
- `exists_atPlace_eq_of_eventually_one`: a family equal to the identity at all
  but finitely many places is the family of local points of an adelic point.

Together with `ext_atPlace`, this is the coordinate form of the bijection in
Getz–Hahn, Proposition 2.3.1, between adelic points and families of local points
lying in the integral points almost everywhere, expressed through regular
function values rather than a chosen faithful representation. The topological
isomorphism of that proposition is not formalized here.

## Continuous lifts of uniformly integral products

For local subgroups `K i`, `IsUniformlyIntegral F G K` means: for every regular
function `a`, at all but finitely many finite places `v`, every element of
`K (.inr v)` has value at `a` in `v.adicCompletionIntegers F`. The finite set of
exceptional places may depend on `a`.

- `IsUniformlyIntegral.isAdelicFamily`: every element of the full product
  `∀ i, K i` is then an adelic family.
- `IsUniformlyIntegral.of_eventuallyEq`: uniform integrality is unchanged when
  finitely many members of the family are replaced.
- `IsUniformlyIntegral.compactProductLift`: the gluing map from the full product
  `∀ i, K i` (product of the subgroup topologies) to `AdelicGroupPoints F G` is
  data of `CoordinateCompactAssembly.CompactProductLift` for the projections
  `atPlace F G i`, so it is continuous with the prescribed local points.

The continuity proof checks each regular function `a` separately, as the
evaluation topology requires. The archimedean component of the glued value is
continuous coordinatewise. For the finite component, uniform integrality gives a
cofinite set `S` of finite places where all values are integral; the finite
component then factors through the restricted product with respect to the
principal filter of `S`, where continuity is coordinatewise
(`RestrictedProduct.continuous_rng_of_principal_iff_forall`), followed by the
continuous inclusion into the finite adele ring
(`RestrictedProduct.continuous_inclusion`).

## Finite adelic points

Assume `G.X.left` is affine.

- `atFinitePlace_eq_finite`: the local point of an adelic point at a finite
  place `v` is the image of its finite-adelic point
  `AdelicGroupPoints.finite F G x` under the point map induced by the
  restricted-product evaluation `RestrictedProduct.evalRingHom` at `v`, viewed
  as an `F`-algebra homomorphism from `FiniteAdeles F` to
  `FiniteCompletion F v`.
- `eventually_atPlace_mem_of_finite`: if every finite-adelic point has image in
  `K (.inr v)` at all but finitely many finite places `v`, then every actual
  adelic point has local point in `K i` at all but finitely many places `i`.

## Provenance

The constructions are derived from the Library's actual adele ring, its
restricted-product structure, and the regular-function evaluation topology on
affine points. Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §2.3, Proposition 2.3.1 (printed p.57), describes the adelic points of
an affine algebraic group as the restricted direct product of local points; this
module implements the coordinate-wise gluing and the continuity statements
needed for the local-to-global argument of Theorem 2.7.1 (printed p.71). Neither
a faithful representation nor the open compact subgroups `K_v` of that
proposition appear here: integrality is tested on all regular functions.
