# Canonical topology on actual full-parahoric multiplication

This derived support unit equips the existing two-factor map
`ParahoricBuildingData.parahoricProductMap` with continuity, without changing
its factors or codomain. It also proves continuity of the existing full
Iwahori multiplication maps and conditional compactness consequences.

The field has arbitrary universe and the existing nonarchimedean local-field
instances. The group and building datum are the actual published objects.
The ambient rational-point topology is explicitly `rationalPointTopology F G.X`;
the centralizer uses the same canonical topology on its own rational points.
Every subgroup has its corresponding subspace topology. There is no
characteristic restriction, positive-rank restriction, or nonempty-root
restriction.

## Constructions and proofs

The centralizer is affine because its actual inclusion is a closed immersion
into the affine group. The imported `continuous_rationalPointMap` proves
continuity of this inclusion on the two canonical rational-point spaces.
Reductivity supplies smoothness and hence local finite type, allowing the
published canonical point topology to make ambient multiplication continuous.

`continuous_parahoricProductMap` composes the coordinate projections, subgroup
inclusions, actual centralizer inclusion, and multiplication. Continuity into
the full parahoric subtype follows from its induced topology.
`parahoricProductContinuousMap` bundles exactly the original function as a
continuous map; its application comparison is definitional. Its surjectivity
is already proved for the same function in `KPParahoricProduct`.

`isCompact_parahoric_of_factors` explicitly assumes compactness of the actual
centralizer-zero subgroup in its own point space and of the actual sharp
fixer in the ambient point space. The established equality of the full
parahoric with their set product, compactness of a continuous image, and
compactness of a product of compact sets prove the conclusion.

Continuity of `iwahoriUnipotentProduct`,
`orderedIwahoriChamberProduct`, and `orderedIwahoriFacetProduct` follows by
the same coordinate argument. The ordered maps use the continuous actual
block maps from `KPRootFixerTopology`; they retain all doubled-root factors.
These continuity results require neither V 7 nor a chamber, facet, sign,
ordering, injectivity, nonemptiness, or decomposition assumption.

The two range-compactness lemmas additionally assume V 7 and compactness of
the supplied centralizer-zero factor. Finite lists of actual relative roots
index compact block subtypes, so the finite product domain is compact.
Continuity makes its range compact. The facet lemma also explicitly retains
a point in the subset to invoke root-fixer compactness. All finite lengths,
including zero, are allowed. The chamber lemma treats both depths; the facet
lemma keeps negative strict depth and positive weak depth as in the original
map.

## Provenance and limits

This is an internal topological consequence of the actual constructions and
the published canonical-point functoriality, topological group operations,
two-factor algebraic comparison, and root-block compactness. It introduces
no new source assertion.

The compactness premises here are separate obligations, not extra premises
for `ChamberIwahoriCompactOpenStatement`. This unit proves neither those
premises nor a range equality for an ordered Iwahori map. It establishes no
ambient openness, structural decomposition, anisotropic compactness, or
compact openness of the full chamber Iwahori from the target's unchanged
hypotheses.
