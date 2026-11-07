# Lifting smooth scheme points over a Henselian local ring

Author: Worker 208.

This module implements the residue-to-integral lifting step in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Theorem 4.5, printed p.12. The registered original source is
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad pulls a smooth map back along a prescribed valuation-ring point and
lifts a rational point of its special fibre using Henselianity.

Here `R` is any commutative Henselian local ring and `K` is any field
presented as a quotient of `R`: the algebra map `R → K` is surjective.
No topology, valuation, completeness, global field, separatedness, or global
finite-type hypothesis is needed. All rings and schemes lie in an arbitrary
common universe `u`.

`exists_smooth_lift_of_residue_point` treats arbitrary schemes `X`, `Y` and
a smooth morphism `f : X → Y`. Given `p : Spec R → Y` and
`q : Spec K → X` whose image is the reduction of `p`, it proves the existence
of `a : Spec R → X` with `a ≫ f = p` and whose reduction is exactly `q`.
In particular, the lift retains the specified morphism on residue fields.

The proof forms the actual pullback `X ×[Y] Spec R`. The pair consisting
of `q` and the canonical `Spec K → Spec R` gives a point of this pullback.
Its projection to `Spec R` is smooth by base change. The published theorem
`Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective`
gives a section through this point. Composition with the other projection
gives `a`; the pullback equations prove both required identities. This
reuses the Library's proof of smooth Henselian section lifting.

`exists_henselian_smooth_point_lift` gives the relative version over any
commutative coefficient ring `C`. The schemes are actual objects of
`Over (Spec C)` and their points are the published `RingPoint` morphisms.
For a surjective `C`-algebra map `φ : R → K`, a prescribed point
`p : Y(R)` and a point `q : X(K)` above its reduction, it gives
`a : X(R)` with `a ≫ f = p` and `RingPoint.changeRing φ a = q`.
The base equation for `a` follows from those of `f` and `p`.

`henselianSmoothPointLift` chooses such an actual `R`-point in the subtype
carrying the two proved equations. The choice uses classical choice and
introduces no alternative point space.

`surjective_integralPointMap_of_surjective_residuePointMap` applies this
construction to every `p : Y(R)`. If the map `X(K) → Y(K)` is surjective,
then `X(R) → Y(R)` is surjective.

These are derived infrastructure results implementing the cited step, with
names and relative-base packaging chosen here. The residue-point
surjectivity premise of the final theorem remains explicit. This module
does not prove a Lang–Weil estimate, almost-all surjectivity at global
places, existence of compatible spreads, or the adelic openness theorem.
