# The fixed part of the induced annihilator quotient

Worker 133. This proof establishes the published
`NonUnitalModuleCornerSimpleStatements.FixedPartInducedQuotientStatement`
with independent ring and corner-module universes.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.3.2, printed pp.20–21 / PDF pp.26–27. Worker 133 read these pages and
the surrounding printed pp.19–22.

The implemented proof follows the source's composition of (I.3.2.1) with
(I.3.2.2). It composes the published corner-linear equivalence
`fixedPartEquivalence e W` with the published equivalence
`IdempotentAnnihilatorComparisons.fixedProjectionEquiv e (Tensor e W)`.
Their forward maps are respectively `w ↦ e ⊗ w` and restriction of the
annihilator quotient projection. Consequently the composite has exactly the
required value `w ↦ [e ⊗ w]`, by definitional equality.

No local-unit or simplicity assumption is used, as in the published target.
The noncomputable choice occurs only in the already published inverse of
the restricted quotient projection. The statement and its import closure
are unchanged.
