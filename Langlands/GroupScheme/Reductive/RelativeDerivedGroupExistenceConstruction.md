# Constructed coroot quotients on every affine pinned model

This internal unit combines the proved local coroot quotient with the
local-to-arbitrary-ring assembly and full geometric-kernel comparison.
It constructs the actual split-model quotient without any additional
mathematical input. Only the final arbitrary-scheme descent implication
retains the separate relative semisimple fppf-perfectness statement.

`relativeDerivedLocalCorootQuotientExistence` proves the precise published
local coefficient-ring input: every affine pinned model with local
coefficient ring has an actual homomorphism to its coroot quotient,
restricting on the coordinate torus to `corootProjection`. The proof
applies `localCorootQuotient` to the model's actual reductive group,
closed fibrewise-maximal coordinate torus and fibrewise root datum. That
construction also gives smoothness and surjectivity; the weaker input
retains its exact torus restriction.

`RelativeDerived.pinnedCorootQuotient M` is an actual chosen homomorphism
from any supplied affine pinned model `M` to the diagonalizable torus of
its integral all-coroot annihilator. There is no locality restriction on
`M.ring`. The definition packages the exact torus restriction, smoothness,
surjectivity, and semisimplicity of the complete kernel of its base change
at every geometric point. It uses classical choice on the proved
`exists_smooth_corootQuotient_of_local`, now with its local premise fully
discharged. The exact restriction permits the full geometric-kernel
comparison `isSemisimple_corootQuotient_geometricKernel`. These kernels
are the actual group-scheme kernels, rather than their identity
components or reduced subschemes.

`relativeDerivedSplitTorusQuotientExistence` proves the entire split
relative torus-quotient existence input in every universe. It applies
the established local-to-split implication to the local construction
proved here. In particular, the quotient target is a relative torus
and the map has all the geometry required by that input.

`relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect` concludes
the unchanged arbitrary-scheme `RelativeDerivedGroupExistenceStatement`
from the single explicit hypothesis
`RelativeSemisimpleFppfPerfectStatement`. It applies the existing
local-to-relative descent bridge to the constructed local witnesses.
The perfectness theorem is used for admissible-subgroup comparison and
descent, and is not proved or silently assumed in this unit. This final
conditional implication is not an unconditional proof artifact for the
host task.

All constructions are uniform in the universe. Neither the arbitrary-ring
quotient construction nor the conditional arbitrary-scheme conclusion
adds a noetherian, reducedness, quasi-compactness, characteristic or
splitness hypothesis to its corresponding supplied-model interface.
The provenance is internal composition of the local construction,
canonical dynamic-cell assembly, actual kernel comparison and
admissible-subgroup descent theorems.
