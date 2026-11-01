# Full strong maps on actual original-chart domains

Author: Worker 36.

This derived construction fixes two actual indexed affinoid atlas presentations
`A` and `B` over a complete ultrametric normed field. It constructs direct
restriction of full strong maps along inclusions of bundled original-chart
domains of `A`, then packages these maps as a presheaf with values in types.
The coefficient, point and chart-index universes remain independent.

The conventions come from Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), section 1.1, printed pp.13–14 / PDF pp.10–11
(induced subset topology, quasinet and net), Definition 1.2.3 and
Remark 1.2.4(i), printed p.16 / PDF p.13 (actual affinoid atlases and
bounded restrictions), and Definition 1.2.7, printed p.18 / PDF p.15
(continuous maps and compatible affinoid morphisms at every admissible
pair). Registered source: `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These pages were reread for this unit. The direct restriction and presheaf
are derived infrastructure for the supplied original atlases, rather than
a separately numbered assertion in the source.

A bundled domain `S` is an actual subset of `A.space` whose contained
original chart ranges form a quasinet on its induced topology.
`A.originalDomainPresentation S` is the published constructed atlas on
that subset. Its indices are precisely the original charts contained in
`S`; its algebras and bounded restrictions remain the original ones.
For `hST : S ≤ T`, a chart `c` in `S` determines the chart
`⟨c.val, c.property.trans hST⟩` in `T`, with exactly the same algebra.

For a full strong map `f` from `A.originalDomainPresentation T` to `B`,
`StrongHom.restrictOriginalDomain_admissible_iff` identifies admissibility
of `c,j` for the composite continuous map with admissibility of that
reindexed chart and `j` for `f`. Its proof expands the two images and
uses the same spectrum point in each. `restrictOriginalDomain` constructs
a map from the literal once-restricted presentation
`A.originalDomainPresentation S` to `B`. Its continuous map is `f.baseMap`
after the actual subset inclusion. Its target existence, every bounded
pullback and each chart square come directly from `f` at the reindexed
chart. Its two-variable restriction equation follows from the corresponding
equation of `f`, translating chart containment through the original
ambient ranges.

`restrictOriginalDomain_apply` records the continuous-map formula.
`restrictOriginalDomain_pullback` records equality of the entire bounded
algebra homomorphism, with explicit admissibility transport.
`restrictOriginalDomain_refl` and `restrictOriginalDomain_trans` prove
identity and successive-restriction laws as equalities of complete
strong maps. Both proofs use the published `ext_of_pullback`: base maps
are definitionally equal, and every bounded pullback is unchanged after
discarding propositional containment witnesses.
`restrictSubspace_restrictOriginalDomain` proves agreement with the
published `restrictSubspace` when `f` is the restriction of an ambient
strong map. This also compares all bounded pullbacks with the same
once-restricted source.

`originalDomainStrongPresheaf A B` assigns
`StrongHom (A.originalDomainPresentation S) B` to `S` in the opposite
of the fixed-original-chart domain inclusion category. Its maps are
direct restrictions. Its functor laws are exactly the full identity and
successive-restriction laws proved above. The target atlas is arbitrary;
no directedness, greatest target chart or reducedness is assumed.

This unit establishes a presheaf. Sheaf descent for arbitrary quasinet
covers, producing local algebra maps, general strong composition, atlas
extension, structure sheaves, étale and equivariant sites and the Harris
tower remain separate obligations.
