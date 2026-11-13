# Standard Lubin–Tate unit parameter data (M358.001/.002/.003/.005)

For `{K : Type u} [Field K]`, a shared
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`
package `F`, and `n : ℕ`, the unit parameter type is the actual quotient
of the valuation-ring unit group by the level-`n+1` higher principal-unit
subgroup. It is a type in `Type u`, with its canonical commutative group.
No uniformizer, chosen root or primitive action enters these definitions.

All names below have prefix `Langlands.NYLL.LubinTate`:

| Source unit | Declaration | Value |
| --- | --- | --- |
| M358.001 | `standardLubinTateUnitParameter` | `F.valuationSubringˣ ⧸ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n+1)` |
| M358.002 | `standardLubinTateUnitParameter_commGroup` | The canonical quotient `CommGroup` instance |
| M358.003 | `standardLubinTateUnitParameterClass` | The quotient homomorphism `QuotientGroup.mk'` |
| M358.005 | `standardLubinTateUnitParameterChosenRepresentative` | A valuation-ring unit chosen from the surjective quotient map over the supplied class |

The commutative-group instance unfolds the parameter type and uses the
Mathlib quotient-group instance. It introduces no second structure on the
underlying units or subgroup. The representative uses `Classical.choose`
on `QuotientGroup.mk'_surjective`; it has the source's explicit arguments
`F`, `n`, and `a : standardLubinTateUnitParameter F n`.

The LocalField and higher-principal-unit definitions are imported by their
canonical Lean modules. Their valuation ring, maximal ideal and complete-DVF
projections are shared with the sibling tasks. The concrete principal-unit
subgroup has carrier `(u : F.valuationSubring) - 1 ∈ F.maximalIdeal^(n+1)`.
The quotient does not require a proof that it is finite to define these data.
Finiteness, cardinality and the chosen-representative identity are separate
obligations; this pair proves none of those theorem targets.

## Original source and modifications

Naganori Yamaguchi, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`:
M358.001 lines 43–46; M358.002 lines 50–56; M358.003 lines 60–64;
M358.005 lines 78–84. Source file SHA-256:
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
Registered snapshot `external-lean-reuse-snapshots-2026-10-21` has content hash
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The four declarations preserve the source names, universe parameters, field
context, binder order and explicitness, types and implementation bodies.
Changes are the `Langlands.NYLL` namespace prefix, this focused module and
its new documentation, and imports of only the shared LocalField,
principal-unit definition and Mathlib quotient-group definitions. Source
imports of PrimitiveAction, PrincipalUnits.Core and Coset.Card and the unused
Polynomial scope are omitted. M358.004 and .006 onward are not included.

The original copyright and author notice remain in the Lean header.
Apache-2.0 licensing and attribution are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`, with source attribution in
`nyll-classfieldtheory-fbd320cd-supplement`.
