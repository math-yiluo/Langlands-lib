# Reduction of additive-character scaling to degree-zero generation

This internal module reduces the unchanged actual virtual scaling statement to
two explicit premises: `CommonClosureDegreeZeroGenerationStatement` and
`GallagherDeterminantStatement`. It does not prove either premise or assert the
unconditional scaling theorem.

For a fixed intermediate field, additive character, Haar measure, field unit
and compatible Weil lift, the proof compares two integer-linear maps from the
actual continuous exact virtual group to the additive synonym of complex units.
The first evaluates the assignment at the scaled additive character. The second,
`correctedScalingValueHom`, multiplies the original value by its exact determinant
at the Weil lift and by the negative-degree power of a complex unit representing
the normalized absolute value. Multiplicativity follows from the published exact
determinant and degree laws and the assignment's additivity. Positivity of the
normalized absolute value constructs the complex unit without a new premise.

Every continuous character of the actual Weil subgroup descends through its
topological abelianization. Transport across the supplied reciprocity equivalence
therefore identifies it with a field character. The concrete rank-one scaling
theorem proves agreement on its actual exact character class.

For an induced difference of two character classes over a larger intermediate
field, the source class has degree zero, and its induction has degree zero.
Choose an additive Haar measure there, whose existence follows from the canonical
local-field topology, and a Weil lift of the included field unit, whose existence
follows from the supplied reciprocity equivalence. Linearity and the two rank-one
identities prove the comparison on the difference. Its zero degree removes the
absolute-value factor.

The system's actual degree-zero induction law moves both assignment values to
the larger field. `traceCharacter_scale` identifies the scaled trace character
with the trace character scaled by the included unit. The determinant-transfer
lemma, conditional on the displayed Gallagher premise and using the system's
normalized reciprocity square, identifies the determinant values at the two Weil
lifts. Thus the two maps agree on every specified induction generator. No
comparison of absolute values between fields is needed.

The generation premise identifies the integer span of these generators with
the full degree-zero kernel. The kernel of the difference of the two linear
maps therefore contains that submodule. Finally, for any virtual class `x`, let
`t` be the trivial character class of degree one. The class
`x - degree(x) • t` has degree zero, and agreement there and on `t` proves
agreement on `x`, including negative virtual dimensions. Coercion from complex
units gives the precise complex-valued conclusion.

`additiveCharacterScaling_of_commonClosureDegreeZeroGeneration` proves this
reduction for one supplied finite p-adic field and system, with independent
field and representation universes. The uniform
`additiveCharacterScaling_of_generation_gallagher` has the unchanged
`AdditiveCharacterScalingStatement` as its conclusion and retains exactly the
two prerequisite statements as additional premises. Neither the target pair
nor its import closure is modified. The proof uses no choice of a system or
reciprocity family and no assertion of their existence.

This is an internal deduction from the existing common-closure generation
formulation, local-constant system laws and helper lemmas. The normalization is
the fixed-Haar formula in Deligne (1973), (5.4), already recorded in the target
and the paired rank-one scaling module. This module supplies the algebraic
extension from rank-one values to the actual exact virtual group rather than
assuming that formula.
