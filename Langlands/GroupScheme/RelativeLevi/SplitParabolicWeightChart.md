# Split charts adapted to a supplied cocharacter

This derived unit constructs actual root chart and weight data over any
commutative ring. The inputs are a reductive group, a fibrewise maximal
coordinate split torus, a finite fibrewise root datum, actual parametrizations
of every root, and any integral coordinate cocharacter `wt`.

`coPairingLinear` is the ordinary dot pairing with `wt`, viewed as an integral
functional on the full character lattice. `exists_base_nonnegative_coPairing`
uses the root datum perfect pairing to express this functional as a coweight,
then chooses a coweight face and its adapted base. Dominance on simple roots
extends by positive-root addition to nonnegativity on every positive root.
This argument does not assume that an abstract root datum pairing agrees
with the coordinate dot pairing.

`SplitParabolicWeightChart` retains a regular cocharacter, an explicit base,
an actual root-height chart on its dynamic contracting group, a bijection
from coordinate indices to the base's positive roots, the exact ambient
composite of every factored root map, and independent natural weight data.
The natural weights equal the pairings with the supplied `wt`.

`nonempty_splitParabolicWeightChart` constructs this data from the inputs.
After choosing an adapted base, it chooses a regular cocharacter positive
on exactly that base's positive roots. The actual split big-cell theorem
and positive-product isomorphism supply the full regular chart. The
`positiveCellRootWeightData` construction supplies the independent weights
and their all-test commutator sum bound. Its definitions give the retained
ambient root formulas and exact pairing values.

Zero weights and an empty root set are allowed. The full regular chart
can include Levi roots with zero `wt` weight. This unit does not identify
its positive-weight subgroup with the dynamic subgroup of `wt` or an
arbitrary supplied radical, establish choice compatibility, or descend
the filtration. Its provenance is the existing coweight-face, split-cell,
actual factored-root and independent-weight constructions; no new original
literature translation is claimed.

The local affine-source instance has the explicit internal name
`splitParabolicWeightChart_affineSource`. This avoids an anonymous declaration-name
collision when this module is imported together with the global root parametrization
infrastructure. Its type, proof and local scope are unchanged.
