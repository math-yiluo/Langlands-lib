# Subgroup of valuation-integer units

`Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup` has the full interface

```lean
(K : Type u) [Field K] [ValuativeRel K] : Subgroup Kˣ
```

It is `MonoidHom.range` of the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K`.
This is the actual image of the units of Mathlib's valuation-integer subring in
field units. The arbitrary universe and both source instances are retained.
No topology, local-field hypothesis, new instance, valuation characterization
or openness theorem is supplied here.

## Source correspondence and changes

M256.001 is `LocalFieldTheory.localBaseUnitSubgroup` at original
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean`,
lines 28–31, definition at line 29. It maps to the public name above. The
original file SHA-256 is
`77d63306c40bd28166878221e43427bbbcd699daeee497bbe40c82935d928f43`.

The docstring, binders and definition body are unchanged. The namespace and
opened inclusion-map namespace gain `Langlands.NYLL`. The full NYLL Basic
import is replaced by published `Basic.U016.Definitions`, which defines exactly
the original map. The module prose is focused on this unit. No patch10 code or
other source declarations are copied.

Focused compilation succeeds using just that prerequisite; the original
module-completion edge to the rest of M128 is unnecessary. The private
full-signature check `a620416a-041d-49b1-9545-b758efc26225` confirms the displayed
arbitrary-universe interface. M256.002–003 remain separate statement/proof work.

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
