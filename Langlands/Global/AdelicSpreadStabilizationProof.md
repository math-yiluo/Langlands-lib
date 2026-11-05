# Eventual stabilization of arithmetic adelic stages

This proof targets `Langlands.Global.AdelicSpreadStabilizationStatement`, the
homeomorphism formulation of the eventual equality in Conrad (2011), printed
p.11, Proposition 4.4. It imports the unchanged target. The two arithmetic
arguments use the actual original-field point equivalences and stage maps.

The ranges of the stage maps increase under inclusion of their finite sets:
this follows from naturality of the actual ring-point cocone. They are open
by `AdelicSpreadStageOpenProof`, and they cover all full adelic points by the
finite-type fixed-model descent theorem. Compactness from
`AdelicSpreadCompactnessProof` and Mathlib's compact directed-cover theorem
give one stage whose range is the whole space. Every larger stage is then
surjective.

Properness of the generic scheme gives separatedness of the generic fibre of
the supplied initial model. `AdelicSpreadEventualSeparationProof` produces a
finite enlargement where the actual base-changed model is separated. For a
stage beyond that bound, the initial-set stage homeomorphism identifies the
original stage with the stage of this separated model. Naturality of that
homeomorphism compares the actual full-adele insertions, and the separated
model's open stage embedding gives injectivity. Taking the union of the
surjectivity and separatedness bounds works at every larger finite level.
Continuity and openness of the actual map, together with this bijectivity,
prove the stated homeomorphism.

The number-field argument keeps the full stage rings, including all infinite
factors. The function-field argument uses finite constants and the specified
rational-function action and scalar tower. The proof adds no separatedness
condition on the initial arithmetic model, no affinity condition and no
nonemptiness condition on the initial finite set. All declarations retain
the target's common universe `u`.

The registered source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011),
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.11, Proposition 4.4. The proof imports the published prerequisites
by Lean name and contributes only this stabilization proof pair. It supplies
this consequence to parent task `886bf565-95e9-4dc6-8a9d-73284a523668`;
the other conclusions of that program remain separate obligations.

Worker 208 authored the shared Lean proof and its original explanation.
Worker 1557 checked the pair against the published target and prerequisites
and prepared it for independent review.
