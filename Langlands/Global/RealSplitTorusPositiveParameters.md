# Positive parameters for actual ordered-coefficient split-torus points

This internal construction gives explicit continuous multiplicative parameters
for the intrinsic positive subgroup of actual points of a supplied split torus.
It also restricts actual characters and actual group-scheme morphisms to the
intrinsic positive subgroups.

## Objects and hypotheses

The coefficient field `A` has `Field A`, `LinearOrder A` and
`IsStrictOrderedRing A`. The notation `(Nonneg A)ˣ` denotes units of the actual
nonnegative subsemiring of `A`; `Units.posSubgroup A` is the subgroup of `Aˣ`
whose values are strictly positive. Their group operations and topologies are
the inherited ones. In particular, the topology on units records both a unit's
value and its inverse.

For actual points, the base field `F`, the coefficient field `A` and the
splitting index type `I` lie in an arbitrary common universe `u`. The
commutative group scheme `T` is over `Spec F`, and `A` has a supplied
`F`-algebra structure. The subgroup
`orderedCoefficientPositiveSubgroup F T A` is imported from
[RealSplitTorusIdentityComponent](RealSplitTorusIdentityComponent.md): its
points are exactly those on which every actual `F`-rational character has
strictly positive value.

The character and morphism restrictions require no splitting or topology.
The parameter construction uses `Fintype I` and a supplied isomorphism of
actual group schemes

```text
e : T.toGrp ≅ splitTorus (Spec F) I.
```

The topological constructions use `TopologicalSpace A`.
The inverse parameter map and its continuity need no additional topological
assumption. Continuity of the forward actual-point map and the final
continuous multiplicative equivalence additionally use `IsTopologicalRing A`.
The actual point topology is exactly
`GroupScheme.affinePointsTopologicalSpace T.toGrp (CommAlgCat.of F A)`;
the positive subgroup has its subtype topology, and parameter tuples have
their product topology.

No order topology, order completeness or `ContinuousInv₀ A` is needed for
these parameter results. With those additional hypotheses as stated in the
imported module, its component theorem identifies the target subgroup with
the actual identity component. For `A = ℝ`, an `F`-algebra structure must still
be supplied; no embedding of an arbitrary number field into `ℝ` is asserted.
Empty `I` is allowed throughout.

## Positive units and actual morphisms

`positiveUnitLift A x hx` lifts a unit `x : Aˣ` with `hx : 0 < (x : A)`
to `(Nonneg A)ˣ`. Its value is the original value of `x`, and its inverse is
the original value of `x⁻¹`, with nonnegativity proved from `inv_pos`.
The two inverse laws are the original unit equations viewed in the subtype.
The lemmas `positiveUnitMap_lift` and `positiveUnitLift_map` prove that this
lift is inverse to the imported inclusion `positiveUnitMap A`.

`positiveUnitEquiv A` packages these maps as

```text
(Nonneg A)ˣ ≃ₜ* Units.posSubgroup A.
```

The forward map is the inclusion with its positivity proof. Its continuity
uses `continuous_positiveUnitMap` and the subgroup topology. For the inverse,
`Units.continuous_iff` reduces continuity to the value and inverse-value
maps into `Nonneg A`. Both come from the continuous value and inverse-value
maps on `Aˣ`, followed by subtype restriction. This explains why continuity
of inversion on the whole coefficient field is unnecessary.

`orderedCoefficientPositiveCharacter F T A χ` restricts the actual character
homomorphism to the positive point subgroup and takes values in
`Units.posSubgroup A`. Its coercion lemma identifies the value with
`Lie.characterValue χ x.val`.

For an actual morphism `f : T ⟶ T'`,
`pointMap_mem_orderedCoefficientPositiveSubgroup` proves preservation of
intrinsic positivity. Given a character `χ` of `T'`, the proof uses positivity
of the pulled-back character `f ≫ χ` and the existing
`Lie.characterValue_comp` formula. `orderedCoefficientPositiveMap` is the
restriction of the genuine point homomorphism using this result; its coercion
lemma is the original `pointMap` formula. These declarations concern actual
scheme morphisms, without a chosen coordinate formula.

## Parameters, evaluation and inverse laws

`orderedCoefficientFull F T A I e` is the group homomorphism from
`I → (Nonneg A)ˣ` to actual affine points. It first applies `positiveUnitMap A`
coordinatewise and then applies the inverse of the existing actual coordinate
equivalence. The lemma `coordinates_orderedCoefficientFull` says exactly

```text
coordinates e (orderedCoefficientFull e x) i = positiveUnitMap A (x i).
```

`orderedCoefficientFull_mem` uses the imported coordinate criterion to prove
that the image is intrinsically positive.
`characterValue_orderedCoefficientFull` gives the actual character formula

```text
χ(orderedCoefficientFull e x)
  = positiveUnitMap A (∏ i, x i ^ characterExponents F I T e χ i).
```

The powers are integer powers in `(Nonneg A)ˣ`. The proof substitutes the
coordinate formula into the imported character monomial formula and uses
preservation of finite products and integer powers by a homomorphism.

`orderedCoefficientParameters F T A I e` reads every actual coordinate of a
positive point, uses the coordinate criterion for its positivity, and applies
`(positiveUnitEquiv A).symm`. Its value after `positiveUnitMap A` is exactly the
original coordinate, as recorded by
`positiveUnitMap_orderedCoefficientParameters`. Continuity is proved
coordinatewise from continuity of the actual coordinate map, coordinate
evaluation, subgroup restriction and the inverse positive-unit equivalence.

The forward map is continuous by continuity of coordinatewise
`positiveUnitMap A` and of the existing inverse actual coordinates.
`orderedCoefficientParameterEquiv F T A I e` consequently gives

```text
(I → (Nonneg A)ˣ) ≃ₜ* orderedCoefficientPositiveSubgroup F T A.
```

Its forward map is `orderedCoefficientFull` with the proved image membership,
and its inverse is `orderedCoefficientParameters`. For the left inverse the
proof compares every coordinate through the injective positive-unit
equivalence. For the right inverse it uses injectivity of the genuine
coordinate equivalence and the coordinate recovery lemma. Multiplicativity
is inherited from `orderedCoefficientFull`. The final coercion lemma
identifies this equivalence's forward value with that original homomorphism
into actual points.

## Provenance and scope

This is internal infrastructure derived from actual character evaluation,
the existing actual split-torus coordinate equivalence and its continuity,
the intrinsic positivity criterion, and elementary unit/subtype constructions.
It introduces no new assertion attributed to the automorphic literature.

The target positive subgroup is defined intrinsically, while the explicit
parameters depend on the supplied splitting. This module constructs no
restriction of scalars, greatest `ℚ`-split central torus, or comparison from
real coefficient points to positive scalar adelic points. It supplies no
unconditional reductive decomposition, Haar measure, height, reduction
theorem or finite-volume result. Those remain separate obligations of the
general adelic program.
