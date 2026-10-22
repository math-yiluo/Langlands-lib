# Proof of algebraic-dual compatibility

`dual_twist` reduces equality of representations to evaluation at a group
element, a linear functional, and a vector. Expanding the dual and twist
definitions gives `f(chi(g⁻¹) • rho(g⁻¹)(v))`. Linearity moves the scalar
outside `f`; the homomorphism inverse law changes it to `chi(g)⁻¹`.
This is the action of `twist chi⁻¹ rho.dual`.
`twistDualCompatibility` proves the entire proposition target by this lemma.

This implementation uses no finite-dimensionality or topology. It proves a
fact about the full algebraic dual, not the smooth contragredient.
The coefficient ring `R`, group `G`, and module carrier `V` retain independent
universes. The only instances are `CommRing R`, `Group G`, `AddCommGroup V`,
and `Module R V`. The closing theorem has the accepted proposition itself
as its result, and introduces every `chi` and `rho` quantified by that
proposition. It neither redeclares the target nor adds a hypothesis.
The target is accepted statement `5c831314-e615-411f-9218-bc54346cef78`
version 1, declaration `Langlands.TwistDualCompatibility`, published at commit
`efa80651ab2c64b6009a54aef0d05f2644b558d7`. Its checked target fingerprint is
`558f3309988ecf9b3c42064d2d08b4e4b3a788e43b67299da218b14c4f490ba0`.
The imported twist definition is accepted artifact
`c83db975-8b79-4fbb-9901-2db836910a0a` version 1, published at
`3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1
(Lean 4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).
The mathematical provenance is explained in `DualStatement.md`.

Worker 4 authored this proof. Worker 7 reused the Lean source unchanged,
verified the current accepted dependency bytes, and expanded this scope
documentation. Native compilation of the dependency, target and proof succeeded.
Inspection of the closing theorem confirmed the full three-universe type;
both proof declarations depend only on `propext` and `Quot.sound`.
These are development checks. Independent proof checking, semantic review,
and publication are separate requirements recorded by their actual receipts.
