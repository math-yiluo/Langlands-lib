# Inversion between the two canonical coset topologies

This derived construction supplies the topological comparison needed when both
existing coset conventions occur. It concerns any group `G : Type u` with a
topology and continuous inversion, and any subgroup `P`; multiplication need not
be continuous. It uses the existing quotient carriers and their quotient
topologies, without a normality or closedness assumption on `P`.

`Langlands.Induction.quotientInversion P` is a homeomorphism from
`Langlands.Induction.LeftQuotient P`, defined using `QuotientGroup.rightRel P`,
to `G ⧸ P`, defined using `QuotientGroup.leftRel P`. Its representative formula
is `[g] ↦ [g⁻¹]` in both directions. These formulas are the lemmas
`quotientInversion_mk` and `quotientInversion_symm_mk`.

The relation comparison is proved from subgroup closure under inversion:
`y * x⁻¹ ∈ P` if and only if `x * y⁻¹ ∈ P`. Mathlib's
`Homeomorph.Quotient.congr` descends the continuous inversion homeomorphism,
proving continuity in both directions for the actual quotient topologies.
The theorem `compactSpace_leftQuotient_iff` transports compactness along this
homeomorphism in either direction.

Two additional generic lemmas express the compact-representative argument.
`compactSpace_quotient_of_compact_representatives` assumes an actual compact
subset `C` with `G = C * P`, expressed pointwise, and proves compactness of
`G ⧸ P`. `compactSpace_leftQuotient_of_compact_representatives` assumes
`G = P * C` and proves compactness of `LeftQuotient P`. Both prove that the
continuous canonical projection maps `C` onto the whole quotient, and apply
compactness of a continuous image. These two lemmas need no continuity of
inversion or multiplication.

Provenance: this is an internal quotient-topology construction derived from the
existing subgroup and quotient definitions and Mathlib's inversion homeomorphism
and quotient homeomorphism construction. It makes no source-literature claim.
For actual dynamic parabolics, the owning rational-point topology must still be
shown to have continuous inversion, and compact representatives or an independent
compactness argument must still be established. This module proves no existence
of an Iwasawa decomposition or compact subgroup and does not prove the general
dynamic-parabolic compactness target.

Author: Worker 125.
