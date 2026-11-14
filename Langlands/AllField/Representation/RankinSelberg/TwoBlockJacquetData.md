# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockJacquetData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockJacquetData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockJacquetData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Two-block scalar sections and absolute Jacquet integral data**

JPSS 1983, Section 4.6, printed pages 410-411: for representations `σ_1, σ_2` of
`GL_(m_1+1)(F)` and `GL_(m_2+1)(F)` with `(m_1+1) + (m_2+1) = t+1`, the sections
of the normalized induction from the lower block parabolic satisfy the
covariance (4.6.1), and the integrand of (4.6.2) is a scalar evaluation of a
section at `u g`, for `u` in the complementary upper radical, against the
positive character of the upper-right corner entry of `u`.

This module defines that data for the published actual lower induction
`F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)` with
`B = succBlockShape m h`: scalar evaluation through supplied linear functionals
on the block carriers, the upper radical matrix, the positive kernel, the raw
integrand, its Bochner integral against a supplied measure and the absolute
integrability conditions. It asserts no convergence.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.Induction.OppositeParabolic`
- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`
- `Langlands.AllField.Representation.Shahidi.Induction`
- `Langlands.AllField.Representation.Shahidi.IntertwiningCovariance`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections` (abbrev): The carrier of the actual lower induction
  `(⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B (B.blockTensor σ)`,
  `B = succBlockShape m h`: the sections of JPSS (4.6.1).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep` (abbrev): The actual lower induced representation `I(σ_1 ⊗ σ_2)`, acting on `Sections`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval` (abbrev): Evaluation of a section at an ambient element.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection` (def): The scalar section `(g, a) ↦ (⊗ ℓ_i) ((σ_1 ⊗ σ_2)(a) f(g))` at an ambient element `g`
  and an actual block Levi element `a`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_one` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval_add` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval_smul` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.sectionEval_zero` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_add` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_smul` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_inducedRep` (theorem): Compatibility with the actual induced right translation.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.scalarSection_covariant` (theorem): The covariance (4.6.1) of scalar sections: if the lower parabolic element `q`
  has Levi projection `b`, then the value at `(q g, a)` is `δ_P(b)^(-1/2)` times the
  value at `(g, a b)`, for the upper block modulus `δ_P`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand` (def): The raw scalar integrand of JPSS (4.6.2):
  `x ↦ ⟨f(u(x) g), ⊗ ℓ_i⟩ ψ(x_(m 0, 0))`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_apply` (theorem): The integrand with the kernel evaluated at the corner entry.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_add` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_smul` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_inducedRep` (theorem): Raw right translation: translating the section by `g'` translates the integrand's
  ambient argument.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction` (def): The function `g ↦ ∫ ⟨f(u g), ⊗ ℓ_i⟩ ψ(u) du` of JPSS (4.6.2), as the ordinary
  Bochner integral against the supplied measure `μ` on the rectangular coordinates.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction_apply` (theorem): The integral written out with the corner kernel.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt` (def): Absolute integrability of the integrand at `g`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable` (def): Absolute integrability of the integrand at every `g`.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction_add` (theorem): Additivity of the integral under absolute integrability of both integrands.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction_smul` (theorem): Complex homogeneity of the integral.
- `Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction_inducedRep` (theorem): Raw right translation of the integral.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockJacquet.tensorContraction`, `Langlands.RankinSelberg.TwoBlockJacquet.tensorContraction_tprod`, `Langlands.RankinSelberg.TwoBlockJacquet.tensorContraction_pairFactorFunctional`, `Langlands.RankinSelberg.TwoBlockJacquet.blockRanks_add`, `Langlands.RankinSelberg.TwoBlockJacquet.index_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.index_one`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_apply_cast`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_add`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_neg`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_sub`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_index_zero_one`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_index_zero_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_index_one_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_index_one_one`, `Langlands.RankinSelberg.TwoBlockJacquet.upperRadical_injective`, `Langlands.RankinSelberg.TwoBlockJacquet.continuous_upperRadical`, `Langlands.RankinSelberg.TwoBlockJacquet.sum_superdiagonal_upper`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_apply`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_eq_superdiagonal_upperRadical`, `Langlands.RankinSelberg.TwoBlockJacquet.norm_positiveKernel`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_add`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_eq_inv_upperJacquetKernel`, `Langlands.RankinSelberg.TwoBlockJacquet.positiveKernel_eq_conj_upperJacquetKernel`, `Langlands.RankinSelberg.TwoBlockJacquet.continuous_positiveKernel`, `Langlands.RankinSelberg.TwoBlockJacquet.scalarSection_of_eval_eq_tprod`, `Langlands.RankinSelberg.TwoBlockJacquet.scalarSection_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.scalarSectionMap`, `Langlands.RankinSelberg.TwoBlockJacquet.scalarSectionMap_apply`, `Langlands.RankinSelberg.TwoBlockJacquet.integrand_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.isAbsIntegrableAt_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt.add`, `Langlands.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt.smul`, `Langlands.RankinSelberg.TwoBlockJacquet.isAbsIntegrable_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable.add`, `Langlands.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable.smul`, `Langlands.RankinSelberg.TwoBlockJacquet.jacquetFunction_zero`, `Langlands.RankinSelberg.TwoBlockJacquet.isAbsIntegrableAt_inducedRep_iff`, `Langlands.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable.inducedRep`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
