# Actual parahorics inside norm-one point fixers

This derived adapter constructs `parahoricCompactStabilizerHom`, the canonical
inclusion of the actual full parahoric `P.parahoric Ω` into
`P.compactStabilizer (P.apartmentMap x)` for `x ∈ Ω`, under the existing
V 7 predicate `P.apartment.IsTopologyCompatible`. It retains the full mapped
`P.centralizerZero` factor and the actual generated sharp fixer.

The field has arbitrary universe `u` and the existing nonarchimedean local-field
instances, with no characteristic or positive-rank restriction. The target
subgroup is the published intersection of the ambient rational-character norm
kernel and the actual point fixer. Its name `compactStabilizer` does not supply
a compactness theorem. This module proves subgroup containment only.

## Provenance

The contribution composes the existing `KPZeroNormKernel`,
`KPFiltrationTopology`, `RationalCharacterTopology`, `ValuationBuildingData` and
`KPParahoric` APIs. It introduces no new source object or building axiom.
The existing parahoric definitions come from KP Definition 7.4.1, while V 7 is
Definition 6.1.2 (printed p.199 / PDF p.230) in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023). Definition 7.4.1 was read on
printed p.255 / PDF p.286. The 1 November 2024 corrections, PDF pp.33–35,
were also read: the change just before Remark 7.4.2 only simplifies singleton
notation, and no corrected Chapter 7 building assertion is assumed here.
The proof below is an internal consequence of these comparisons; it
makes no assertion that a separate compact-openness theorem from the book has
been proved.

## Implemented proof

`filtration_le_rationalCommonNormKernel` uses compactness of the actual root
filtration in the canonical topology `rationalPointTopology F G.X`. Every
compact subgroup lies in the ambient rational-character norm kernel by
`compactSubgroup_le_rationalCommonNormKernel`. An element of a root fixer at
`Ω` lies in the zero-depth filtration at `x ∈ Ω`; the subgroup supremum defining
the sharp fixer therefore lies in the same kernel. Antitonicity of sharp fixers
and the existing point-fixer inclusion place it in the fixer of `x` as well.
These two inclusions give `sharpFixer_le_compactStabilizer`.

`map_centralizerZero_le_compactStabilizer` applies the actual zero-subgroup
norm-kernel inclusion in the same centralizer. V 6, already bundled in
`ParahoricBuildingData`, maps this factor into the norm-one point fixer. Taking
the join with the sharp fixer yields `parahoric_le_compactStabilizer`. The point
specialization and ambient norm-kernel containment follow. The bundled
homomorphism restricts the original subgroup inclusion; its coercion is the
identity on the underlying rational point.

The explicit membership `x ∈ Ω` is essential; no claim is made for the empty
subset. The result assumes neither compactness nor openness of the full
parahoric or point fixer. Closedness, full-subgroup boundedness, centralizer
compactness and the exact chamber compact-openness target remain separate
obligations.
