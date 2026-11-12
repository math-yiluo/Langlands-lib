# Continuity target for inclusion of valuation-integer units

`Langlands.NYLL.LocalFieldTheory.integerUnitsToFieldUnits_continuousStatement`
is the unproved proposition

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop :=
Continuous (integerUnitsToFieldUnits K)
```

Here the inclusion is the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`,
from the actual valuation-integer units to field units. Mathlib supplies the
subtype topology on the valuation-integer ring and the canonical unit-group
topologies. The arbitrary universe, explicit K and three instance parameters
are retained. There is no continuity premise, nonarchimedean-local-field
hypothesis or valuation/topology compatibility hypothesis. This module states
the target and contains no theorem proving it.

## Source correspondence and changes

M255.003 is original `LocalFieldTheory.integerUnitsToFieldUnits_continuous` in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`,
lines 60–67, theorem at line 62. It maps to the public `Statement` name above;
the future exact proof retains the source theorem name. The original file
SHA-256 is `8cd7c49384a442469cff5bf0397150f52b24b03fa3087b3b252b29e9e05b38a8`.

The source theorem becomes a Prop-valued `def`, its proof is omitted and its
name gains `Statement`. Its binders and conclusion are unchanged. The public
and opened namespaces gain `Langlands.NYLL`. The full source NormUnits and
Basic imports and the analytic/matrix imports are replaced by published
`Basic.U016.Definitions` and `Mathlib.Topology.Algebra.Group.Units`. The module
prose is focused on this unit. No new instance or patch10 code is introduced.

Focused compilation and declaration inspection
`a34fe010-36f4-476d-862a-d2c6e8d4b210` succeed and report
`statement_returns_prop: true`. The smaller imports suffice without the norm
continuity targets/proofs M255.001–002 or the rest of M128. Proof publication
remains a separate obligation after this target is in the Library.

## Attribution

The source is Naganori Yamaguchi's ClassFieldTheory, assisted by OpenAI Codex,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The original copyright and author header is retained. The explicit modification
record credits Worker 120 (10 November 2026). The unchanged Apache-2.0 files are
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
No file-specific NOTICE entry or patch10 change applies to this unit.
