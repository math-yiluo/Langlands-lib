# NYLL M225.001: higher principal-unit subgroups

This construction defines the concrete level-`n` principal-unit subgroup
of the units of the valuation ring of a complete discrete valuation field.

## Definition and parameters

The declaration is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`.
Its parameters are `{K : Type u} [Field K]`,
`(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K)`,
and `(n : ℕ)`. Its value is a `Subgroup F.valuationSubringˣ`,
with carrier
`{u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}`.
The field and value-group universes are retained. This is a subgroup
construction with values in `Type`, rather than a proposition.

The valuation ring and maximal ideal are the published complete-DVF
projections from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`.
No new complete-DVF structure or global instance is introduced.

The construction proves that the identity belongs to the carrier by
`1 - 1 = 0` and ideal membership of zero. Closure under multiplication
uses `xy - 1 = x(y - 1) + (x - 1)` and the ideal's multiplication and
addition laws. Closure under inversion uses
`x⁻¹ - 1 = -(x⁻¹(x - 1))` and the ideal's multiplication and negation
laws. These closure proofs are the source implementation.

## Source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Filtration.lean`,
M225.001, declaration at line 43 and implementation at lines 44–81.
The source file SHA-256 is
`26c1fdb63f9766b4dd8e6f43e2c7c0d97593a3afb0df2e9d5b8a129d0f5ed4bb`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 311 extracted M225.001 into this focused module and added the
`Langlands.NYLL` namespace prefix. The import is the published
complete-DVF projections, replacing the source imports of Complete,
ResidueField, CharP lemmas, and Units.Hom; those other source units are
unneeded for this construction. Unused source `open` and `open scoped`
commands are omitted, while `noncomputable section` and both universe
declarations are retained. The subgroup definition, binder order,
explicitness, and closure proofs are unchanged. The module comment is new.

The original copyright and author header is retained, with the
Apache-2.0 license and attribution in the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
