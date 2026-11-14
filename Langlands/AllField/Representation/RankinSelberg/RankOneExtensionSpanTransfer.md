# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanTransfer` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Transfer layer for the strict rank-one extension span comparison**

The bookkeeping half of JPSS (1983), Lemma (5.5): from a pointwise identity
`Ψ_ind(s) = c Ψ_base(s)`, with `c ≠ 0` and the induced integral absolutely
convergent on a right half-plane, deduce the inclusion of the Laurent spans of
the actual zeta values. The rank equations of `unequalRankZetaValuesAt` are
unpacked through an explicit rank cast of Whittaker functions, and the casts are
evaluated on the concrete block matrices of `RankOneExtensionAnalyticData`.
No analytic comparison is proved here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionSpanComparison_of_pointwise` (theorem): The transfer in the shape of `RankOneExtensionSpanComparisonStatement`, with the
  trailing index `k` and both rank equations arbitrary; the statement is the instance
  `k = r - t - 2` with its proofs `hrBase` and `hrInd`. The only extra premise is the
  pointwise comparison of the actual zeta integrals: every convergent block-one
  integral of `π × σ₁` is, on a right half-plane, a nonzero constant multiple of an
  absolutely convergent block-zero integral of `π` against the lower induction.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankCastWhittaker`, `Langlands.RankinSelberg.rankCastWhittaker_apply`, `Langlands.RankinSelberg.rankCastWhittaker_rfl`, `Langlands.RankinSelberg.mem_unequalRankZetaValuesAt_iff`, `Langlands.RankinSelberg.zetaSpan_le_of_forall_exists_const_mul`, `Langlands.RankinSelberg.hasRationalContinuation_of_eq_const_mul`, `Langlands.RankinSelberg.zetaSpan_unequalRankZetaValuesAt_le_of_pointwise`, `Langlands.RankinSelberg.rankInclusion_entry`, `Langlands.RankinSelberg.rankOneExtensionLowerBlock_eq_mul`, `Langlands.RankinSelberg.rankOneExtensionEmbeddedLowerBlock_eq_mul`, `Langlands.RankinSelberg.reindex_symm_unequalRankMatrix_one`, `Langlands.RankinSelberg.reindex_symm_appendIdentity_reindex`, `Langlands.RankinSelberg.determinantWeight_reindex_finCongr`, `Langlands.RankinSelberg.rankCastWhittaker_unequalRankMatrix_one`, `Langlands.RankinSelberg.rankCastWhittaker_appendIdentity_reindex`, `Langlands.RankinSelberg.rankCastWhittaker_appendIdentity_lowerBlock`, `Langlands.RankinSelberg.unequalRankIntegrand_rankCast_one_mk`, `Langlands.RankinSelberg.unequalRankIntegrand_rankCast_zero_mk`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
