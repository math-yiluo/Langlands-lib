# Proof of the actual adelic-level model comparison

Authors: Worker 208 (Lean proof and Markdown); Worker 1525 (check and
Markdown refinement).

`adelicLevelModelComparison` proves exactly
`AdelicLevelModelComparisonStatement` in its arbitrary common universe.
The two component theorems preserve the five independent hypothesis
clauses for the actual curve-place and full number-field level point maps.

For the set assertions, each published `...LevelModelPointMap_eq`
identifies the actual arithmetic map with `localProductPointMap` after
the explicit S-integer algebra equivalence of coefficient rings.
`ringPointChangeRingEquiv` is an equivalence on actual scheme points.
The published local-product comparison therefore gives injectivity under
quasi-separatedness, surjectivity under affineness, and surjectivity under
quasi-compactness because the actual factor rings are local (the
published instances `instAdelicLevelModelPoints4` and
`instAdelicLevelModelPoints9`; the infinite completions are fields).
Combining
injectivity and surjectivity gives bijectivity under quasi-compactness
and quasi-separatedness. No finite-type or Noetherian premise is used
or inferred in these arguments.

For topology, `curvePlaceLevelFactorAlgEquiv_isHomeomorph` composes
the published level product homeomorphism with Mathlib's
`Homeomorph.sumPiEquivProdPi` in the reverse direction.
`numberFieldLevelFactorAlgEquiv_isHomeomorph` uses two such reindexings,
including the identity homeomorphism of the existing infinite-adele
factor. Thus both explicit algebra equivalences preserve precisely
the published adelic-level and factor-product topologies.

The generic helper `ringPointChangeRingEquiv_isHomeomorph` applies
`affineSchemeCoefficientContinuity_proof` to the algebra equivalence
and its inverse. Their coefficient maps are continuous because the
original equivalence is a homeomorphism. The existing inverse laws
on actual points supply a bundled homeomorphism, so the affine
point topologies are preserved in both directions. Finally composition
with `localProductPointMap_isHomeomorph` proves the claim for the
original arithmetic point map. The proof does not redefine any point
topology by the desired comparison.

The derived provenance is Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.6–8, Theorem 3.6 and
formulas (3.6.1)–(3.6.2), with the actual-level conventions on printed
p.1. Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implemented proof reuses the published generic geometric argument
and the independently proved arithmetic level topology comparisons.

This proves the stated level comparisons only. It does not provide the
Noetherian S-integer realization, the finite-type consequences for the
source models, model descent, nonaffine point topologies, transition
maps, the adelic colimit or independence of the initial model. Those
remaining obligations are unchanged from the statement's Markdown.
