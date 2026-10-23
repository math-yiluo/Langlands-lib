# Conditional descent to actual idele-class cohomology

This module constructs an invariant for a fixed Galois extension `E/F` of
number fields in an arbitrary common universe. It retains the supplied local
invariant family `I` and assumes `RelativeImages`, with explicit choices of
places above the finite and infinite places of `F`.

The construction has three additional inputs. A selected finite place must
have completed extension degree equal to the global degree. Reciprocity
`SumOfInvariantsVanishes I x` must hold for every field-unit degree-two
cohomology class `x`. Finally, the actual idele-class degree-two cohomology
group must be finite, with cardinality at most the global degree. Finiteness
is an explicit typeclass assumption; the cardinality inequality alone does
not imply it.

`ideleClassInvariantEquivOfFullLocalDegree` is an additive equivalence from
the actual `relativeIdeleClassCohomology F E 2` onto the degree denominator
subgroup of the rational numbers modulo integers. Composing it with the
subgroup inclusion defines `ideleClassInvariantOfFullLocalDegree`. The module
proves that this map is injective, has exactly that subgroup as its range,
and agrees with the total idele invariant after the actual quotient
cohomology map. It also proves that the quotient cohomology map is
surjective under these same hypotheses.

The derivation is internal. The local finite lift realizes any denominator
value because its local degree equals the global degree; the total-lift
evaluation from `IdeleTotalSection` proves surjectivity of the total
invariant with restricted codomain. Reciprocity and the existing
kernel-vanishing theorem supply the kernel inclusion needed by
`FiniteInvariantDescent`. The equivalence `denominatorEquiv` identifies the
denominator subgroup's cardinality with the positive global degree.
The finite cardinality argument in `FiniteInvariantDescent` then both forces
the quotient map onto and constructs the desired equivalence. The remaining
lemmas use that equivalence and the subgroup inclusion.

This is conditional supporting work. It does not establish any of the three
additional inputs, choose such data for all extensions, or prove the
restriction, inflation, or local compatibility laws of
`GlobalInvariantStatement`. In particular, no surjectivity claim is made for
an arbitrary Galois extension without the listed hypotheses.
