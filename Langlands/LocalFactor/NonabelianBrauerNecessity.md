# Arithmetic kernel compatibility forced by an actual system

This is an internal consequence of the published system laws and the actual
Brauer presentation. It proves necessity of `KernelCompatibility`; it supplies
neither a system nor the arithmetic theorem needed to construct one.

`systemValue` writes an additive assignment as an integer-linear map from the
original continuous exact virtual group to the additive version of complex
units. The existing multiplicativity law and its zero-value consequence define
an additive homomorphism, whose integer linearity is automatic.

For a supplied full system, rank-one agreement with the original complex-valued
abelian expression identifies the unit on each reciprocal character line with
the published `abelianEpsilonUnit`. Equality of complex units follows from
equality of their complex values.

For an actual nested-field generator, the difference of its two character lines
has degree zero. The original induction law evaluates its induced class at the
trace-pulled additive character and the supplied source-field Haar measure.
Integer linearity evaluates the difference as subtraction, which is division
of the two actual abelian units. This proves `systemValue_generatorClass`
against the unchanged `generatorValue`.

Equality on all integer singleton presentations proves
`evaluationMap_eq_systemValue_comp`: the whole abelian evaluation is the
composition of the actual virtual presentation with this system value.
Consequently a presentation representing zero evaluates to zero, the
multiplicative unit. `kernelCompatibility_of_system` packages exactly this
kernel containment, retaining every field, character, Haar family and the
independent representation universe of the published predicate.

Finally, `kernelCompatibility_of_exists` applies the original existence
proposition only after receiving its existing normalized reciprocity premise.
It therefore proves the necessity implication with the original conditional
telescope. This proof uses a system as an input to a necessity theorem; it
cannot discharge the arithmetic compatibility prerequisite for existence.
