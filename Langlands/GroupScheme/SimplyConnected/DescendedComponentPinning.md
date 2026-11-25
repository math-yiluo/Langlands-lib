# The exact descended group realizes the entire prescribed Cartan component

Derived from actual normal-factor descent, original-field
torus projections, the geometric scalar-extension comparison, actual factor
Galois pinnings, and the equivalence of factor fibres with entire Cartan
components. For a simply connected ambient group, the actual group descended
from the chosen geometric factor to its full stabilizer field receives a genuine
Galois pinning. Its whole simple vertex set is equivalent to the entire prescribed
original Cartan component. Every ordered integral Cartan entry and every full
relative Galois star action are preserved. The construction retains literally
the published stabilizer field and its actual descended group model. It proves
existence of the precise input to the actual Tits-index/full-lift conversion.

`descendedComponentPinning` chooses this actual complete comparison from the
proved nonempty result, retaining the exact group and extension.

`ComponentPinningWithProjection` also records the retraction of the
extended ambient group onto that factor and the compatible maps of tori.
The projection's section is the actual descended subgroup inclusion.
After the root-datum comparison for scalar extension, the projection
inflates each factor simple root to the vertex specified by the original
Cartan component comparison.

`nonempty_descendedComponentPinningWithProjection` constructs this witness
for the original geometric factor descent. The group retraction comes from
the normal factor of the ambient group over the stabilizer field. The tower
base-change comparison recovers the original geometric inclusion, and the
factor projection construction retains the corresponding simple-root map.
The original existence theorem follows by taking the pinning comparison
from the resulting witness.
