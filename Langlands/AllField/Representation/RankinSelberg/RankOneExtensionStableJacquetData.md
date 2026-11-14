# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionStableJacquetData`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionStableJacquetData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionStableJacquetData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionStableJacquetData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Stabilized lower Jacquet data for the strict rank-one extension**

JPSS (1983), Lemma (5.5), printed page 424, formula (1): the Whittaker functional
of the lower induction is the limit, over an exhaustion by compact open subgroups,
of truncated integrals of the scalar contraction of a section against the character.
This module defines the actual scalar integrand on the row coordinates of the upper
cell, its compact-open stable graph, the domain of sections where it stabilizes, the
linear stable value on that domain and a conditional extension. It asserts no
stabilization for any particular section.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionLowerTranslate` (def): The actual induced right action of `h` on the section carrier, transported through
  `asModuleEquiv`.
- `Langlands.AllField.RankinSelberg.rankOneExtensionStableIntegrand` (def): The scalar integrand `y ↦ ℓ(f(u(y) g)) ψ(y_last)` on the row coordinates of the
  complementary upper cell, with the positive character.
- `Langlands.AllField.RankinSelberg.rankOneExtensionStableIntegrand_apply` (theorem).
- `Langlands.AllField.RankinSelberg.rankOneExtensionStableIntegrandMap` (def): The integrand at a fixed ambient element, as a complex linear map of the section.
- `Langlands.AllField.RankinSelberg.rankOneExtensionStableIntegrandMap_apply` (theorem).
- `Langlands.AllField.RankinSelberg.rankOneExtensionStableIntegrand_translate` (theorem): Translating the section by `h` under the actual induced right action replaces the
  ambient element `g` by `g * h`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneExtensionRow_exists_compactOpen`, `Langlands.RankinSelberg.rankOneExtensionLowerTranslate_asModuleEquiv`, `Langlands.RankinSelberg.rankOneExtensionLowerSectionEval_translate`, `Langlands.RankinSelberg.HasRankOneExtensionStableJacquetAt`, `Langlands.RankinSelberg.HasRankOneExtensionStableJacquetAt.unique`, `Langlands.RankinSelberg.hasRankOneExtensionStableJacquetAt_translate_iff`, `Langlands.RankinSelberg.rankOneExtensionStableDomainAt`, `Langlands.RankinSelberg.rankOneExtensionStableDomain`, `Langlands.RankinSelberg.mem_rankOneExtensionStableDomainAt`, `Langlands.RankinSelberg.mem_rankOneExtensionStableDomain`, `Langlands.RankinSelberg.rankOneExtensionStableDomain_eq_top_iff`, `Langlands.RankinSelberg.rankOneExtensionLowerTranslate_mem_stableDomain`, `Langlands.RankinSelberg.rankOneExtensionStableDomain_le_at`, `Langlands.RankinSelberg.rankOneExtensionStableDomainTranslate`, `Langlands.RankinSelberg.rankOneExtensionStableValueAt`, `Langlands.RankinSelberg.rankOneExtensionStableFunctional`, `Langlands.RankinSelberg.rankOneExtensionStableDomainTranslate_val`, `Langlands.RankinSelberg.hasRankOneExtensionStableJacquetAt_stableValueAt`, `Langlands.RankinSelberg.rankOneExtensionStableValueAt_eq_iff`, `Langlands.RankinSelberg.hasRankOneExtensionStableJacquetAt_stableFunctional`, `Langlands.RankinSelberg.rankOneExtensionStableFunctional_eq_iff`, `Langlands.RankinSelberg.rankOneExtensionStableValueAt_translate`, `Langlands.RankinSelberg.rankOneExtensionStableFunctional_translate`, `Langlands.RankinSelberg.rankOneExtensionStableExtension`, `Langlands.RankinSelberg.rankOneExtensionStableExtension_apply`, `Langlands.RankinSelberg.hasRankOneExtensionStableJacquetAt_stableExtension`, `Langlands.RankinSelberg.rankOneExtensionStableExtension_eq_iff`, `Langlands.RankinSelberg.hasRankOneExtensionStableJacquetAt_stableExtension_translate`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
