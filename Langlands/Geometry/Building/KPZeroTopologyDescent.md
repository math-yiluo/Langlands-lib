# Canonical topology and descent of the actual zero subgroup

This internal adapter uses the published topology `fixedFieldTopology F` on the
actual inertia fixed field `UnramifiedClosure F`. The inclusion from the supplied
nonarchimedean local field `F` is continuous: the fixed-field topology is induced
from the spectral-norm topology on the separable closure, and the inclusion into
that closure is a continuous normed-algebra map. No completeness of the fixed
field is assumed.

`unramifiedRationalExtensionContinuousHom` bundles the existing
`GaloisPointComparison.rationalExtend` continuously between the named canonical
rational-point topologies. It uses the generic scalar-extension comparison and
requires only that the group scheme is affine. This construction preserves the
existing point carriers and map.

`isOpen_anisotropicZeroPoints_of_isOpen` identifies the actual descended
subgroup with the inverse image of `E.zeroPoints` under this continuous map.
Thus it descends openness, conditional on openness of that actual unramified
zero subgroup. Establishing the premise is a separate remaining proof
obligation; this module does not prove compact openness of a centralizer.

The provenance is internal composition of published field and point-topology
comparisons, intended for openness descent of the actual KP zero subgroup.
