# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Assembly of the rank-one extension span comparison**

JPSS (1983), Lemma (5.5), printed pp. 423–427. For a Whittaker function `W₀` of `π` and an
inverse Whittaker function `W'` of `σ₁`, the scalar cutoff of `W₀`, a compact section `f` of the
lower induction `I(σ₁, χ)` and the lower Jacquet functional `Λ` give a Whittaker function `W₁`
of `π` and the inverse Whittaker function `W''(g) = Λ(I(g) f)` with
`Ψ_ind(s; W₁, W'') = C ρ(U) Ψ_base(s; W₀, W')`. The change of variables is
`rankOneExtensionUnfoldingCore`; this module verifies its hypotheses for
`H(z) = W₁(ι z) c_f(z) |det z|^(s - (k+1)/2)`.

The disintegration of the quotient measure and the Jacquet functional enter as the hypotheses
`LowerBlockQuotientDisintegrationStatement` and `RankOneExtensionLowerJacquetFunctionalStatement`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.CentralSpectralElement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCompactSectionProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDisintegration`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionWhittakerCells`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionUnfoldingFunction_lowerBlock_mul_upperCell` (theorem): JPSS (1983), Lemma (5.5), printed 425–426: on the cell `B(m, x, a) u(y)`, the function
  `H(z) = W₁(ι z) c_f(z) |det z|^(s - (k+1)/2)` is `1_U(a) · W₀(B(m, x, 1)) W'(m)
  |det m|^(s - (k+2)/2) · φ(y)`.
- `Langlands.AllField.RankinSelberg.continuous_rankOneExtensionUnfoldingFunction_of_continuous` (theorem): The function `H(z) = W(ι z) c(z) |det z|^s` is continuous for smooth `π` and
  continuous `c`.
- `Langlands.AllField.RankinSelberg.continuous_rankOneExtensionUnfoldingFunction` (theorem): The function `H` with the scalar coefficient `c_f` of a lower section is continuous.
- `Langlands.AllField.RankinSelberg.continuous_rankOneExtensionLowerCoefficient` (theorem): The inverse Whittaker function `g ↦ Λ(I(g) f)` of a lower section `f` is continuous.
- `Langlands.AllField.RankinSelberg.rankOneExtensionSpanComparison_pointwise` (theorem): JPSS (1983), Lemma (5.5), printed pp. 423–427, pointwise form. Let `W₀` be a Whittaker
  function of `π` and `W'` an inverse Whittaker function of `σ₁` whose block-one integral
  `Ψ_base(s; W₀, W')` converges absolutely on a right half-plane. Then there are a Whittaker
  function `W₁` of `π` (the scalar cutoff of `W₀`), an inverse Whittaker function `W''` of the
  lower induction (`W''(g) = Λ(I(g) f)` for a compact section `f` and the Jacquet functional `Λ`),
  and a constant `c = C ρ(U) ≠ 0` with `Ψ_ind(s; W₁, W'') = c Ψ_base(s; W₀, W')` and absolute
  convergence of the block-zero integral on the same half-plane. The disintegration of the
  quotient measure and the Jacquet functional are the hypotheses `hdis` and `hJ`.
- `Langlands.AllField.RankinSelberg.rankOneExtensionSpanComparison_of_statements` (theorem): `RankOneExtensionSpanComparisonStatement` from the lower-block disintegration of the
  quotient measure and the lower Jacquet functional.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.determinantWeight_mul_of_det_eq_one`, `Langlands.RankinSelberg.rankOneExtensionUnfoldingFunction`, `Langlands.RankinSelberg.rankOneExtensionUnfoldingFunction_lowerBlock_mul`, `Langlands.RankinSelberg.rankOneExtensionUnfoldingFunction_upperCell_mul`, `Langlands.RankinSelberg.mul_eq_integral_of_integrable_mul`, `Langlands.RankinSelberg.nullSingletonClass_of_map_mul`, `Langlands.RankinSelberg.continuous_rankOneExtensionScalarLower`, `Langlands.RankinSelberg.lowerScalarEntry_one`, `Langlands.RankinSelberg.isCompact_preimage_lowerScalarEntry`, `Langlands.RankinSelberg.determinantWeight_lowerBlock_mul_upperCell`, `Langlands.RankinSelberg.sqrt_inv_mul_cpow`, `Langlands.RankinSelberg.continuous_dual_apply_of_isSmooth`, `Langlands.RankinSelberg.integral_dirac_of_subsingleton`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
