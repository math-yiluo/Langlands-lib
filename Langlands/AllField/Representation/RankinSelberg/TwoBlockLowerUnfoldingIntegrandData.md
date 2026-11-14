# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The integrand of the Section 4.7 lower unfolding**

JPSS (1983), Section 4.7, equation (1), printed pages 412-413: the right side is the
integral over `H_(t_1,t_2) \ G_r` of `f[g; e, e] W(w' g) |det g|^s (gΦ)~[ζ, η]`, where
`w' = w_r diag(w_(t_1), w_(t_2))`, `ζ = (1, 0, …, 0)`, `η = (0, …, 0, 1)` and
`Φ~(ξ, v) = ∫ Φ[(w, v)] ψ(ξ ᵗw) dw` integrates the first block of a row.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space, a Schwartz–Bruhat function `Φ` and a supplied
additive Haar measure `μ`, this module constructs the partial Fourier value
`g ↦ (gΦ)~[ζ, η]`, proves its explicit formula and the absolute integrability of its inner
integrand, and constructs the unweighted scalar function

`[g] ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`

on the published quotient `H⁻ \ GL_(t+1)`, `C = w'`, by actual quotient descent. The three
covariance laws under `H⁻` (scalar section, partial Fourier value and `W(C ·)`) and their
cancellation are proved. The weight `|det g|^s`, outer measurability, outer integrability and
the Section 4.7 identity are not part of this module.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.scalarSection_lowerBlockUnipotent_mul` (theorem): Left translation by `u ∈ H⁻` multiplies the scalar section at the Levi identity by the
  product of the two block inverse standard characters of the diagonal blocks of `u`. The
  lower-left block of `u` is arbitrary; the half modulus is one because the diagonal blocks are
  unipotent.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.whittaker_blockRotation_lowerBlockUnipotent_mul` (theorem): `W(C u g) = ψ_(H⁻)(u) W(C g)` for `u ∈ H⁻`: `C u C⁻¹` is upper unipotent with standard
  character value the lower character of `u`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.isTopologicalRing_carrier` (theorem): The canonical topology makes `F` a topological ring.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure` (theorem): Every additive Haar measure on `F` is σ-finite, since `F` is locally compact and second
  countable.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.partialSection` (def): The partial Fourier value `(gΦ)~[ζ, η]` of JPSS (4.7.1): the plus-sign first-block
  integral of the row translate `x ↦ Φ(x g)` at `ξ = ζ`, second block `η`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.partialSection_apply` (theorem): The explicit formula
  `(gΦ)~[ζ, η] = ∫ ψ(w_0) Φ((w, η) g) dw` for the supplied product measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.rowMeasure_map_vecMul_upperUnipotent` (theorem): Right multiplication by an upper unipotent matrix preserves the supplied product row
  measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.partialSection_lowerBlockUnipotent_mul` (theorem): `(u g Φ)~[ζ, η] = ψ(-corner(u)) (gΦ)~[ζ, η]` for `u ∈ H⁻`: the unipotent change
  `w ↦ w n_a` preserves the measure and the first coordinate, and the translation by the last
  row of the lower-left block contributes the inverse corner phase.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.groupIntegrand` (def): The unweighted scalar function `g ↦ W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]` on `GL_(t+1)`,
  before descent.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.groupIntegrand_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.groupIntegrand_lowerBlockUnipotent_mul` (theorem): Left `H⁻`-invariance: the two positive block characters and the positive corner phase of
  the lower character from `W(C ·)` cancel the inverse block characters from the scalar
  section and the inverse corner phase from the partial Fourier value.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand` (def): The unweighted integrand of JPSS (4.7.1) on the actual quotient `H⁻ \ GL_(t+1)`: the
  actual descent of `groupIntegrand`. No coset representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_mk` (theorem): Representative formula: `integrand [g] = W(C g) ⟨f(g), ⊗ ℓ_i⟩ (gΦ)~[ζ, η]`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_mk_eq_groupIntegrand` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerUnfolding.zeta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.eta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.zeta_apply`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.eta_apply`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.rowPairing_zeta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.vecMul_eta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.vecMul_upperUnipotent_zero`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.rowPairing_vecMul_upperUnipotent_zeta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.corner`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.corner_def`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.cornerRow`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.cornerRow_zero`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.vecMul_join_eta`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.partialSection_def`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.partialSection_integrable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
