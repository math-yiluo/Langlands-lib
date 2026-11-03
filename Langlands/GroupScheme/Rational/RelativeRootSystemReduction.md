# Relative-root-system assembly from four explicit structural inputs

Author: Worker 1225.

`RelativeRootSystemReductionStatement.{u}` is the conditional implication from
four geometric statements to the existing `RelativeRootSystemStatement.{u}`.
The theorem `relativeRootSystemReduction` proves this implication using
`relativeRootSystem_of_remaining_structural_statements`. This is an internal
supporting reduction; the unconditional relative-root-system assertion remains
unproved here.

The published theorem `relativeRootSignInclusions` discharges the sign input of
`positiveRootStabilizerReduction`. The other inputs remain explicit:
`RelativeRootReflectionExistenceStatement`, `ParabolicDynamicStatement`,
`ParabolicSelfNormalizerStatement`, and `GenericCentralizerStatement`.
The reduction assumes these four statements and does not prove them.

For an arbitrary field and connected reductive group with a maximal split torus,
the proof obtains integral reflection data from the first premise, finite actual
roots and a generic cocharacter from the published split-torus results, and a
trivial positive-root stabilizer from the other three premises and the published
sign theorem. The published chamber-generation construction then gives the full
`HasRelativeRootSystem` predicate, including the actual quotient action's
faithfulness and Weyl image. Smoothness, affineness, and the torus inclusion's
monomorphism are derived from the original hypotheses.

Only the reflection data from the first premise are needed for the chamber
construction; that premise's additional full scheme-kernel centralization
property is preserved in its type but unused by this assembly. No separate
root-negation premise, quotient-finiteness premise, root-system premise, or
faithfulness premise is introduced.

The construction retains arbitrary universes and fields and does not require a
nonempty or reduced root system. Its provenance is the named published
constructions and deductions. In particular, genericity and root finiteness
come from `IsSplitTorus.exists_genericCocharacter` and
`IsSplitTorus.finite_relativeRoots`; stabilizer triviality comes from
`positiveRootStabilizerReduction`; and the root pairing, exact root range,
Weyl image, and faithful action come from
`RelativeRootReflectionData.hasRelativeRootSystem_of_positive_stabilizer`.

The remaining geometric proof obligations include the corrected CGP route for
reflection existence. This reduction asserts no new external geometric theorem
and does not resolve the host task's Milne-errata obligation. Discharging the
four explicit inputs with independently accepted proofs would permit a theorem
whose type is the unconditional exact host target.
