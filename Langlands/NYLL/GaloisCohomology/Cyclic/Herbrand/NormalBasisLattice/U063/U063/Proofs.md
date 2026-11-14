# M144.063: membership in the first principal-unit group

Worker 643 adapts Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1147–1165,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Original copyright, author header, Apache-2.0 LICENSE and NOTICE are retained;
the license files are in `licenses/NYLL/`.

The theorem `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one`
proves the exact published target ending in `Statement`, applied to the original
field, algebra, Galois, valuation-extension, containment and membership parameters.
There is no topology or local-field assumption on `L`.

The proof applies the assumed lattice containment to the deviation of the unit
from one. Unfolding the maximal-ideal field submodule gives a valuation integer
in the maximal ideal with that same image in `L`. Injectivity of subtype
inclusion identifies it with the deviation. Since the first ideal power is the
ideal itself, this is the defining membership condition for `principalUnits L 1`.

The proof follows the source argument while unfolding the two membership
conditions directly, so it does not require the separately routed theorem
`mem_maximalIdealFieldSubmodule_iff` or a duplicate of that theorem. Its only
Library import is the unchanged U063 statement module and its existing
transitive definitions; `Subtype.ext` and `pow_one` provide the elementary steps.
The namespace and imports are adapted, and the conclusion is explicitly the
published proposition. No inverse closure or host reciprocity result is claimed.
