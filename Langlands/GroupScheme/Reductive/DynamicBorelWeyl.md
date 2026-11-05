# Positive-root stabilizers for a supplied generic dynamic Borel

This internal derived module works with a connected reductive group over an
algebraically closed field, an actual maximal split torus, and a generic
cocharacter. An actual Borel subgroup representing the dynamic parabolic of
that cocharacter is an explicit hypothesis. No existence of such a Borel
or classification of all parabolics is assumed.

A normalizer class preserving the positive relative roots has a rational
representative normalizing the dynamic parabolic. This follows from the
published relative-root-sign inclusion theorem and the existing geometric
normalizer argument. The supplied representative of that parabolic
identifies it with the Borel. All-test normalizer membership implies
normalization of its rational points. The published exact Borel normalizer
theorem places the point in the Borel itself.

Because the point also normalizes the torus, the published dynamic
parabolic argument places it in the dynamic centralizer of the generic
cocharacter. The published exact generic-centralizer theorem identifies
this with the full torus centralizer. Its class in the actual rational
normalizer quotient is therefore the identity. This proves
`hasTrivialPositiveRootStabilizer_of_dynamicBorel`.

Triviality of that stabilizer makes the actual quotient action on the
rational root span injective. The definition
`relativeWeylActionEquivOfDynamicBorel` uses this injectivity to construct
a group equivalence between the actual quotient and the image of its
action. Its forward map is exactly `relativeWeylAction`, as the
accompanying evaluation identity states. This equivalence needs no
supplied reflection data.

If actual integral reflection data are also supplied, the published
chamber-generation construction now gives the complete
`HasRelativeRootSystem` predicate. It includes both generation of the
actual quotient by the reflection representatives and faithfulness on
the actual rational root span. The second theorem packages this
consequence, with all reflection data still explicit.

The proof discharges positive-root-sign, Borel-normalizer and
generic-centralizer results using their published exact proofs. It retains
the actual torus, cocharacter and Borel throughout. It constructs no
negative-rho character or highest-weight representation and proves no
Steinberg irreducibility. Its provenance is the implemented deduction
from these published Library results.
