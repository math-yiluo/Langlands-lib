# Smooth connected-fibre arithmetic models

Author: Worker 109. The model construction adapts the published
`AdelicSpaceProperModelReduction` of Workers 129 and 157, with its comparisons
from Workers 208 and 105.

This internal unit constructs smooth morphisms with nonempty geometrically
connected fibres over one ring of integers from the corresponding actual
morphism over the global field. Both characteristics and arbitrary supplied
separated finite-type source and target models are retained. There are no
limit-descent propositions as additional hypotheses.

The common-stage theorem first descends smoothness, then descends geometric
connectedness at that stage. Smoothness survives the second base change.
Canonical iterated-base-change isomorphisms place both properties at the same
composite incoming stage. The reverse implication pulls both properties back
from its common witness. The inputs are the independently published
`spaceLimitSmoothDescent` and `spaceLimitGeometricallyConnectedFibresDescent`.

The general model theorem conjugates the limit morphism by the supplied fibre
identifications and applies `spaceLimitMorphismDescent`. The published
`compIso_hom_comp_eq` converts its section equality to an equality of arrows.
After transport through the comparison isomorphisms, common-stage descent
supplies the required geometric properties. Naturality preserves the exact
commuting square with the original morphism. The separatedness and
finite-presentation atlas hypotheses survive base change.

For each arithmetic branch, take the union of the original finite sets and
base change both original models to that ring of integers. The published
Noetherianity of the original integer rings upgrades their finite-type
atlases to finite-presentation atlases. The actual integer-ring spectrum
diagram has the field spectrum as its limit. Applying the general model
construction gives separated finite-type models, the identified generic
fibres, a smooth morphism with nonempty geometrically connected fibres and
the exact commuting generic-fibre square. The curve finite set contains the
original nonempty source finite set; number-field finite sets may be empty.

This gives model geometry only. It does not supply a uniform Lang-Weil
estimate, fixed fibre dimensions or their varying-dimension decomposition,
or the final assertion about adelic openness. The full eight-property
limit-descent theorem is not used or inferred. The provenance is internal
composition of the named published results; the proof follows the earlier
proper-model construction while supplying the smooth and connected-fibre
inputs unconditionally.
