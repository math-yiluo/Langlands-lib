# Two remaining inputs to the common-witness existence proof

This internal conditional assembly preserves the arbitrary universe and all
common witnesses of `JointSpecialCompactBasisExistenceStatement`. Its main
result, `jointSpecialCompactBasisExistence_of_availability_and_basis`, has
exactly two explicit inputs: corrected KP assignment existence
(`BruhatTitsAvailabilityStatement`) and
`AvailableSimultaneousStandardBasisStatement`. Neither is proved here. The
result remains an implication and does not complete Task 4169.

The implemented proof takes a globally valid assignment from the first input,
uses published `validAssignmentTorusRebasing` to base it at the original
maximal split torus, and obtains a special vertex using published
`availableSpecialVertexExistence`. The second input supplies the compact
properties, Levi inheritance and simultaneous basis at that same point.
Published `Iwasawa.availableIwasawa` supplies the ambient products. The
companion `JointBasisCartanAssembly` derives the ambient and same-compact
Levi Cartan comparisons from global validity and published results, so a
separate Cartan statement premise is no longer required.

For each actual standard Levi, published `availableSpecialLeviCompact`
supplies available data whose torus is the prescribed torus and whose special
compact subgroup equals the original ambient compact's Levi intersection.
The available Iwasawa theorem applies there, and
`parabolicPointProductFamily_of_heq` transports its conclusion through the
torus equalities. Finally `joint_of_valuationBuildingData` assembles all
clauses at one apartment, point and centralizer datum.

The earlier `jointSpecialCompactBasisExistence_of_remainingInputs` is retained
as the direct seven-input reduction with four inputs filled by published
proofs; it still displays a redundant separate Cartan premise. The two-input
result is the improved route. No change is made to the published target or
any of its imported pairs.

The provenance is internal composition of the named published results and the
explicit centralizer transport in the companion module. It makes no additional
claim from original literature; source and scope information remains in the
published pairs of the underlying results.
