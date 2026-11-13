# NYLL M225.008: the zero-level target

For a complete discrete valuation field `F`, the level-zero principal-unit
subgroup is the whole unit group of its valuation ring.

## Exact target

The declaration is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_topStatement`.
Its telescope is `{K : Type u} [Field K]`,
`(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K)`,
and its proposition is `higherPrincipalUnitGroup F 0 = ⊤`.
Both universes, all source parameters, and their explicitness are retained.
The definition of the subgroup comes from the focused M225.001 module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`.
There is no additional mathematical hypothesis.

## Source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Filtration.lean`,
M225.008, lines 175–178, with the shared field parameters at lines
40 and 85 and the defining subgroup at lines 43–81.
The source file SHA-256 is
`26c1fdb63f9766b4dd8e6f43e2c7c0d97593a3afb0df2e9d5b8a129d0f5ed4bb`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 311 extracted the proposition into a focused module, added the
`Langlands.NYLL` namespace prefix, replaced the source theorem by a
`Prop`-valued definition with suffix `Statement`, and imported only the
subgroup construction. Unused source opens and the noncomputable section
are unnecessary for this proposition and are omitted. The module comment
and docstring are new. The source theorem's `simp` attribute belongs to
the eventual proof, rather than to this proposition definition.
No theorem, helper result, or global instance is introduced.

This pair supplies only a statement. The source proof route uses subgroup
extensionality and simplification of the zeroth ideal power, without
the intervening source M225.002–.007 results.
The original copyright and author header is retained; the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` supply the Apache-2.0
license and attribution.
