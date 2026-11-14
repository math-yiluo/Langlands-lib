# Spreading parabolic containment with a specified relative torus

This internal composition extends SplitTorusContainment from a globally split
torus to a supplied relative torus maximal on every actual residue fibre.
The two subgroup inclusions are relative parabolics in a reductive group over
an arbitrary scheme. Their actual subgroup ranges are assumed to be contained
at one residue fibre. The conclusion is containment on an open neighbourhood of
that original point, on every test scheme.

`range_le_fieldPoint_of_residueFiber` transports residue-fibre range
containment to a supplied field-valued point with the same image. It factors
that point through the canonical residue field, applies monotonicity of subgroup
base change, and uses the canonical comparison between successive and direct
pullbacks. This lemma needs no parabolicity, smoothness or reductivity.

`exists_open_range_le_of_torus_residueFiber` takes the etale splitting cover
in the relative-torus predicate and chooses a point above the distinguished
base point. ParabolicTransport preserves the two relative parabolics on this
cover member, while reductivity is preserved by base change. The preceding
lemma transfers the original range containment to its residue fibre. The
published field-point maximality theorem and the torus pullback comparison
transfer maximality of the specified torus to that same fibre.

SplitTorusContainment then supplies an open of the cover member. Its composite
map to the original base is etale. Canonical pullback comparisons express the
proved containment along this composite, and EtaleContainment descends it to
the composite's open image. The chosen point maps to the original point, so the
image is the required neighbourhood.

`torusParabolicContainmentNeighbourhood` selects an actual open together with
the proved membership and range containment. This derived construction uses
only the named Library interfaces and the accompanying transport and split
containment prerequisites. It does not assume a Lie containment hypothesis;
that field-level implication is the separate input for the final target proof.
