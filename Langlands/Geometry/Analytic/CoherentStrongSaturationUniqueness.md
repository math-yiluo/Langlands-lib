# Uniqueness of the constructed whole-atlas extension

For original strong-map data `f`, `IsSaturationExtension f F` says that the
enlarged strong map `F` has precisely the same continuous map and recovers
every original admissible bounded pullback. The heterogeneous equalities
account only for the proved original-chart representative identifications.
This is a property of an output extension, not an input to its construction.

Under the original-map law `f.HasCoherentPullbacks`, the actual construction
`saturationExtension` satisfies this property. Every enlarged source chart
is contained in the whole original parent of its chosen representative.
Choose an original target for that parent. The strong restriction equation
from the enlarged source to the parent determines its bounded pullback to
this target from the recovered original bounded pullback. This argument
identifies the constructed and competing maps to one target per enlarged
source chart. The proved saturated-source extensionality theorem identifies
the complete strong maps, including every other admissible target pullback.
No equality of algebra maps is inferred solely from spectrum points.

`existsUnique_saturationExtension` combines this uniqueness with the already
constructed extension. This is an internal consequence of actual saturation,
its naturality equations and the previously proved saturated-source recovery.
It retains the explicit intrinsic coherence premise on the original maps;
no equivalence with external strong-morphism conventions or unrestricted
extension theorem is asserted.
