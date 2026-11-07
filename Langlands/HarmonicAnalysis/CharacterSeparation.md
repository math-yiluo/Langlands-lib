# Discrete character separation and open principal units

This module shares the established helpers originally implemented in
`Langlands.HarmonicAnalysis.UnboundedConductorProof`. Integration moved their
proofs unchanged into the namespace
`Langlands.HarmonicAnalysis.CharacterSeparation`, exposing the separation and
openness theorems for reuse. The rational-circle map and its injectivity lemma
remain private.

## Character separation

The private additive homomorphism `rationalCircleMap` sends the class of a
rational number modulo the integers to its real class modulo the integers.
Its injectivity proof uses the quotient's zero criterion: if the real image is
an integer, injectivity of rational-to-real casting shows that the original
rational number is the same integer.

For an arbitrary discrete abelian group `G` and a nonidentity element `g`,
Mathlib's
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero` separates
`Additive.ofMul g` by a character to `AddCircle (1 : ℚ)`, the rational circle.
Composing this character with `rationalCircleMap`, `AddCircle.toCircle`, and
`Circle.toUnits` gives a multiplicative homomorphism to `ℂˣ`. The rational
circle embedding and `AddCircle.injective_toCircle` prove that its value at
`g` is not one. Its continuity follows from discreteness of `G`; continuity
of the rational-circle character with its own topology is unnecessary.
This is the exported theorem
`Langlands.HarmonicAnalysis.CharacterSeparation.exists_discrete_character`.

## Open principal units

For any specified topological data `T`, the theorem
`Langlands.HarmonicAnalysis.CharacterSeparation.principalUnits_isOpen` proves openness of every published subgroup
`T.principalUnits n`. The valuation-one condition is the pullback of an open
sphere of the actual canonical valuation, transported through
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. The second condition
is the pullback of the open valuation integer ring by
`u ↦ (u - 1) / T.uniformizer ^ (n : ℤ)`.
The published `mem_principalUnits_iff_div_mem_integers` identifies the
intersection with `T.principalUnits n`. This argument also covers level zero
and adds no topological group hypothesis to the theorem.

## Uses and provenance

The unbounded-conductor proof uses these helpers on a quotient beyond a chosen
positive level. `Langlands.LocalFactor.RankOneStabilityCoset` uses them on the
quotient at a prescribed level to prove bounded-conductor separation. The
shared theorems retain arbitrary discrete abelian groups and arbitrary supplied
p-adic topological data, respectively; the openness theorem includes level zero.

Worker 649 implemented the rational-circle embedding and discrete separation.
Worker 655 independently supplied the character-module separation route and
its open-quotient design. The openness proof adapts Worker 394's
`isOpen_principalUnits` implementation, as documented in the original
`UnboundedConductorProof.md`. Worker 1813 reused these helpers in the accepted
rank-one coset contribution. Integrator extracted the common implementation
without changing its mathematical statements or proofs.
