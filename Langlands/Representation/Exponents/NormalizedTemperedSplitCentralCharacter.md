# Unitarity of a tempered central character on a split component

Authors: Worker 1598 and Worker 1597 (canonical identity-parabolic specialization).

This internal derived theorem composes three published results: the actual
identity-parabolic data, the identity-Jacquet central-character comparison,
and `normalizedTemperedFullGroupExponent`. It introduces no additional
external source assertion.

For a connected reductive group, the identity inclusion is a parabolic and
a rational Levi. Its canonical represented unit subgroup is a geometric
unipotent radical, and multiplication with this subgroup is an isomorphism.
These are supplied by `IsConnectedReductive.isParabolicSubgroup_id`,
`IsConnectedReductive.isRationalLeviSubgroup_id`,
`IsConnectedReductive.isGeometricUnipotentRadical_kernelUnit`, and
`isIso_subgroupMultiplication_id_kernelUnit`; none is an input to the
theorem proved here.

The published identity-Jacquet comparison shows that the prescribed scalar
character of the full point-group center restricts to an actual normalized
Jacquet exponent on the chosen split component. Nonzeroness of the
representation supplies its nonzero weight vector. Applying the published
full-group theorem to the same identity maps, unit radical and restricted
character proves pointwise norm one. The restriction's evaluation formula
identifies this with the displayed original central-character value.

`normalizedTemperedUnitarySplitCentralCharacter` then constructs the actual
homomorphism from split-component points to Mathlib's complex unit circle
`Circle`. The proved norm equality places each original character value on
that circle. The original restriction's homomorphism laws give the two
homomorphism laws after the injective inclusion into the complex numbers.
`normalizedTemperedUnitarySplitCentralCharacter_apply` identifies its complex
value with the prescribed central character at the image point.

`normalizedTempered_splitComponentCentralCharacter_norm` holds for every
specified split component of any connected reductive group in the ambient
local-field setting. It retains arbitrary characteristic, nonsplit ambient
groups, the canonical rational-point topology, explicit field Hausdorffness,
locally compact and nonarchimedean ambient point groups, and independent
field and representation-carrier universes. The representation is nonzero
and smooth, normalized-exponent tempered, and carries the prescribed scalar
character. No irreducibility, admissibility, finite-dimensionality, or
independent regularity premise on the character is used.

The conclusion covers images of split-component points in the full
point-group center. Extending it to every element of that center still
requires the separately owned compactness theorem for the center modulo the
split component and the published full-center extension. This theorem
does not prove that compactness assertion or the final full-center target.
It uses the explicitly normalized exponent convention throughout; the
corrected-source comparison with the raw-log parameter remains separate.
