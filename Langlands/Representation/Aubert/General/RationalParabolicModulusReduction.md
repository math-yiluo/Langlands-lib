# The actual parabolic modulus comparison from Levi unimodularity

Author: Worker 53. The imported closedness helper is by Worker 103.

This internal reduction specializes the semidirect modular-character
calculation to the literal standard rational-point subgroups of the
published `RationalParabolicModulusStatement`. It is a conditional helper,
not a proof of that target: intrinsic unimodularity of the literal standard
Levi remains an explicit hypothesis. It does not assert ambient reductive
unimodularity.

`standardParabolic_modularCharacter_of_levi` has the field, connected
reductive group, maximal split torus, generic cocharacter, standard
cocharacter statement, closedness, point-topology instances, and continuous
Levi projection of the exact target. Its only further hypothesis is that
Mathlib's modular character on the literal `levi i ν I` is identically one.
The local compactness needed to state this hypothesis is derived from the
closedness of the parabolic and continuity of the actual Levi projection.

The proof derives second countability of the actual ambient rational points
from their finite-type affine point topology. The closed unipotent and
parabolic subgroups are locally compact. The continuous Levi projection
identifies the Levi inside the closed parabolic with an equalizer, giving
its closedness and hence local compactness. The published
`standardUnipotent_isUnimodular_of_standardCocharacterStatement` supplies
triviality of inner Haar modulus on the unipotent subgroup. The generic
`modularCharacter_eq_restrictCharacter_of_unimodular` then computes the
parabolic modular character. Finally `closedRestrictCharacter_eq`
identifies the result with the exact closed-subgroup wrapper in the target.

The provenance is the internal specialization of the imported topology,
standard-unipotent, and semidirect-product results. No Cartan decomposition,
compact quotient, or modular-character continuity result is used here.
