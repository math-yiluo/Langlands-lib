# Compact comparison for the original represented orbit stabilizer

This internal adapter specializes the natural compact-comparison family to
the actual full stabilizer of the original represented orbit. It retains an
explicit simultaneous dynamic realization of the original parabolics in
the datum's common torus.

The intermediate subgroup is the inverse image, under the original target
Levi projection, of the literal intersection of the target Levi image with
the inverse-conjugated source parabolic. Its kernel containment follows
from the definition. The intersection is closed because both original
point-image subgroups are closed, and the saturation is closed by
continuity of the original projection. Closedness of the full orbit
stabilizer follows from closedness of the original source parabolic.

The original target Levi section sends every saturation Levi point to the
full stabilizer. Its projection is the original point, whose saturation
membership gives precisely the required conjugate-parabolic membership.
Under the explicit dynamic realization, the stabilizer projection image
theorem places the entire full stabilizer in this same saturation.

`orbitCompactComparison` supplies these proved conditions to
`representedCompactComparison`. Its output is the existing natural family
for every smooth representation of the full original stabilizer and every
morphism between such representations. The source uses the original
target projection-kernel coinvariants of compact induction; the target
uses compact induction from the saturation's actual Levi subgroup with
the existing literal nested-kernel Haar-ratio correction and original
coefficient quotient action.

All measure, compact-open basis and integration inputs remain those
already derived by the represented compact-comparison construction. No
closedness, section, kernel-containment or stabilizer-containment premise
is supplied externally. The dynamic realization remains explicit. This
module does not identify the remaining Haar-ratio character with the
original normalized intersection characters, compare the final
coefficient action, or prove the closed local orbit comparison.
