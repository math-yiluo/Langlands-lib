# Closed immersions on actual arithmetic-level model points

## Target and mathematical scope

`Langlands.Global.AdelicLevelModelClosedImmersionStatement` asserts that
postcomposition with a closed immersion of arithmetic models induces a closed
embedding on their actual adelic-level point spaces, endowed with the published
`curvePlaceLevelModelPointTopology` or `numberFieldLevelModelPointTopology`.
The target model is finite type: the separate Lean assumptions are
`LocallyOfFiniteType Y.hom` and `QuasiCompact Y.hom`. Its closed subscheme is
therefore also finite type. Neither model is assumed affine or separated.
The map is the actual map of relative scheme morphisms, `p ↦ p ≫ f`.

The curve branch uses every actual curve place and its completion, with the
completed valuation ring outside the arbitrary finite set `S`. It retains the
original `k → RatFunc k → F` scalar tower and a finite-dimensional function-field
extension, including inseparable extensions. Finite constants are unnecessary
for this closed-embedding assertion and are not assumed. The number-field branch
includes all infinite completions and all finite places, with integral factors
outside `S`. Empty finite sets are allowed in both branches; the infinite
number-field factors are always present.

## Source and provenance

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Printed p.9, Corollary 3.7 and the opening paragraphs of Section 4 use the
closed-embedding property of the level construction and its passage to full
adelic points. The level topology is the product topology of Theorem 3.6.

This is a derived focused target for the level step of that argument. The
published topology is induced by the actual local-model point comparison; the
level comparison theorem and local closed-immersion theorem are the intended
inputs to its proof. The arbitrary-constant curve version records the broader
scope of that product argument. It does not assert the closed-embedding property
for the full final topology; that passage remains a separate obligation.

This file supplies a proposition-valued statement, not a proof.
