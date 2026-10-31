# A unique rational fiber of a proper map has a finite target neighborhood

`Langlands.AlgebraicGeometry.UniqueRationalFiberFiniteNeighborhoodStatement`
is a universe-polymorphic proposition definition. It states the following
supporting geometric assertion and supplies no proof.

## Maps and hypotheses

Fix an arbitrary universe `u`. The field `K : Type u` is algebraically closed,
and `X Y : Scheme.{u}` are schemes. The structure morphisms are

- `p : X ⟶ Spec (CommRingCat.of K)`; and
- `q : Y ⟶ Spec (CommRingCat.of K)`.

Both are locally of finite type, expressed by `LocallyOfFiniteType p` and
`LocallyOfFiniteType q`. The actual scheme morphism `f : X ⟶ Y` is proper,
expressed by Mathlib's `IsProper f`. The compatibility `f ≫ q = p` makes it a
morphism over `K`. Properness is required of `f`; neither structure morphism
is required to be proper.

The specified morphism `x : Spec (CommRingCat.of K) ⟶ X` satisfies the
published predicate `Picard.IsRationalPoint p x`. This means exactly
`x ≫ p = 𝟙 (Spec (CommRingCat.of K))`. In particular, it is an actual rational
point over the given structure morphism, rather than just a point of the
underlying topological space. The over-base compatibility implies that
`x ≫ f` is a rational point of `Y` over `q`.

The uniqueness hypothesis quantifies over actual morphisms
`x' : Spec (CommRingCat.of K) ⟶ X`. If `Picard.IsRationalPoint p x'` and
`x' ≫ f = x ≫ f`, it requires `x' = x`. Thus uniqueness concerns only the
rational fiber above this specified rational point of `Y`. No uniqueness
condition is imposed on any other fiber. The equality in this hypothesis is
an equality of scheme morphisms, rather than just equality of underlying
points.

## Conclusions

Write `c = IsLocalRing.closedPoint K`, the unique point of `Spec K`,
`z = x c`, and `y = f z`. The conjunction in the statement has two parts.

1. `f ⁻¹' {y} = {z}` as sets in the underlying space of `X`. The inverse-image
   set includes every topological point over `y`, not just rational or closed
   points. The conclusion identifies that entire fiber with the singleton
   consisting of the specified point `z`.
2. There exists an open subset `V : Y.Opens` such that `y ∈ V` and
   `IsFinite (f ∣_ V)`. Here `f ∣_ V` is the actual restricted scheme
   morphism from the open subscheme on `f ⁻¹' V` to the open subscheme on
   `V`. It is finite on the entire preimage of this target neighborhood.

The second conclusion is stronger than finiteness on a chosen source
neighborhood of `z`. The first conclusion concerns the underlying topological
fiber; it makes no assertion that the scheme fiber is reduced, has length
one, or is isomorphic to `Spec K`.

## Scope and limitations

The universe and the characteristic of `K` are arbitrary. Non-reduced schemes
are allowed. There are no tangent, smoothness, reducedness, irreducibility,
stalk-surjectivity, immersion, or extra finite-fiber premises. There is no
separate assumption that `X` or `Y` is separated over `K`; properness of `f`
retains its usual separatedness requirement for that morphism. There is no
closed-immersion conclusion or claim about fibers away from `y`. The specified
rational point already makes `X` nonempty whenever these hypotheses are
instantiated.

## Internal provenance

Worker 487 supplied the shared Lean draft. This module preserves that Lean
statement unchanged. The formulation is derived internally from the published
rational-point predicate in
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation` and the pinned
Mathlib APIs; it is not a transcription of an external theorem.

The supporting API locations in Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are:

- `Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`:
  `pointEquivClosedPoint`, `pointOfClosedPoint`, `pointOfClosedPoint_comp`,
  `pointOfClosedPoint_apply`, and `ext_of_apply_closedPoint_eq` relate closed
  points to actual rational points of a scheme locally of finite type over
  an algebraically closed field.
- `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`:
  `LocallyOfFiniteType.jacobsonSpace` supplies the relevant Jacobson property.
- `Mathlib/Topology/JacobsonSpace.lean`: `closure_inter_closedPoints` and
  `JacobsonSpace.closure_inter_closedPoints_eq_closure` express density of
  closed points in the relevant closed or locally closed subsets.
- `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`:
  `exists_isFinite_morphismRestrict_of_finite_preimage_singleton` gives an
  open target neighborhood with finite entire restriction for a proper
  morphism whose topological fiber is finite.

These APIs suggest a later proof: the rational points `x` and `x ≫ f` give
closed points `z` and `y`. Closed points in the closed set `f ⁻¹' {y}`
correspond to rational points of `X`, and uniqueness of the specified rational
fiber forces all of them to be `z`. Jacobson density then identifies the
whole topological fiber with `{z}`. Its finiteness permits the cited Mathlib
finite-neighborhood lemma to give the second conclusion. This paragraph
explains the origin of the formulation; none of these proof steps is proved
by this module. The statement does not assume the downstream local
closed-immersion criterion or any projectivity or very-ampleness result.
