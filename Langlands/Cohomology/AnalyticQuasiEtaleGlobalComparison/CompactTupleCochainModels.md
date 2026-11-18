# Analytic finite cochain models from compact lifted tuple cones

This internal construction connects `FiniteTupleEquivariantModel`,
`AnalyticFiniteLiftDiagramSections` and `FiniteFreeCochainModels`. A finite
quasi-étale cover by compact objects admitting action lifts is supplied,
together with actual limiting tuple cones in every positive tuple length,
compact lifted basis representatives, and isomorphisms from the cone points to
those representatives. Compact-lift compatibility remains an explicit
hypothesis. None of these geometric data are constructed in this module.

For a given degree and ordinary cochain, `finiteFreeModelOfCompactTupleCones`
collects the tuple representatives in the three adjacent chain degrees into a
finite disjoint union. Its edges are all faces in the two intervening
boundaries. Each vertex gets a continuous local action lift from its membership
in `CompactLiftBasis`. The sections assigned to the middle vertices are exactly
the values of the cochain under the canonical finite free-term comparison; the
other vertices get zero sections.

The common finite-diagram construction chooses an open subgroup below any
prescribed bound on which every face is equivariant and all supplied sections
are fixed. The resulting normalized global lifts are eventually equivariant
for the actual compact lift system of this subgroup, by compact-lift
compatibility. They feed `finiteFreeThreeTermModelOfCones`; its ordinary
differential squares are proved by the imported tuple-cone presentation
identities. Its middle comparisons and actions agree with those used to fix the
supplied sections. Thus the resulting actual finite signed model satisfies
`FixesCochain` for the specified cochain. The construction returns both the
subgroup and model, fixedness, and inclusion in the prescribed bound.

`exactAt_of_compactTupleCones` adds the full-group finite-equivariant-refinement
and size hypotheses, and injectivity of the coefficient in the quasi-étale equivariant category.
The actual cover arrow is locally surjective, so the published free Čech
augmentation result gives ordinary positive-degree exactness. The finite-model
constructor then supplies the models for every cocycle required by
`exactAt_of_openSubgroupFiniteFreeModels`. That theorem proves exactness of the
ordinary module-valued Hom complex using injectivity after actual open-subgroup
restriction.

The provenance is internal: finite disjoint unions of supplied objects and
face maps, existing simultaneous shrinking, and the existing finite-model
descent theorem. This module proves a conditional Hom-exactness assertion. It
does not discharge compact-lift compatibility or existence of compact lifted
tuple cones, and it does not assert the global comparison theorem.
