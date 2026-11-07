# Transporting closed-fibre rational sections to finite-field-valued points

Author: Worker 208.

This is derived infrastructure for the final paragraph of the proof of Theorem
4.5 in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.13. It transports an actual rational section of a
closed fibre to an actual lift of a prescribed finite-field-valued point. The
source is registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For a morphism `p : Spec K ⟶ B`, let `b` be the image of the unique point of
`Spec K`. The construction `liftFieldPointFromResidueSection` takes a section
`s : Spec κ(b) ⟶ Y_b` of the fibre's structure morphism. It constructs
`Spec K ⟶ Spec κ(b) ⟶ Y_b ⟶ Y`, using Mathlib's residue-field homomorphism
`B.descResidueField (Scheme.stalkClosedPointTo p)`. The fibre equation and
Mathlib's exact factorization of `p` through `Spec κ(b)` prove that the constructed
morphism `q` satisfies `q ≫ f = p`. This construction applies to every field
`K`, without finiteness, closed-image, smoothness or base finiteness hypotheses.

The auxiliary theorem `isClosed_image_of_finite_field` proves that `b` is closed
when `K` is finite and `B` is locally of finite type over `Spec (ULift ℤ)`.
The Library theorem `NoetherianApproximation.isJacobsonRing_int`, transported
along `ULift.ringEquiv`, makes the base Jacobson, hence also `B`. The map from
the spectrum of the finite field to the integer base is locally of finite type.
Cancellation gives that `p` is locally of finite type. Mathlib's preservation of
closed points over a Jacobson target then gives the result. Quasi-compactness of
`B` is unnecessary for this auxiliary theorem.

The homomorphism `κ(b) → K` is injective because its source is a field.
`finite_residueField_of_fieldPoint` uses this injection to prove finiteness of
`κ(b)` for finite `K`; `card_residueField_le_of_fieldPoint` proves
`Nat.card κ(b) ≤ Nat.card K`.

The main definition `uniformLangWeilLargeResidueFieldPointLifts` takes the full
proposition `UniformLangWeilStatement` as an explicit proof parameter. It retains
each of that statement's geometric hypotheses: `B` is locally of finite type
over the integers and quasi-compact; `f` is smooth, separated, surjective,
locally of finite type and quasi-compact; its fibres are geometrically connected
and all have the given pure dimension `d`. It returns a positive real constant
`C` and, for every finite field `K` and every `p : Spec K ⟶ B` satisfying
`C² < Nat.card κ(b)`, an actual `q : Spec K ⟶ Y` together with `q ≫ f = p`.
It uses `uniformLangWeilLargeResidueSections` for a section over the now-proved
closed point `b`, then applies the transport construction.

The threshold is on `κ(b)`. The cardinality inequality above does not turn a
lower bound on `Nat.card K` into a lower bound on `Nat.card κ(b)`: for example,
points of `Spec 𝔽₂` can have values in arbitrarily large extensions of `𝔽₂`
while their image has residue field `𝔽₂`. Thus this unit supplies the
closed-image and exact transport steps, and records the precise scope of the
threshold. The uniform estimate itself, its extension to all large fields of
values, the global finite-exception assertion and adelic openness remain
obligations of the parent task.
