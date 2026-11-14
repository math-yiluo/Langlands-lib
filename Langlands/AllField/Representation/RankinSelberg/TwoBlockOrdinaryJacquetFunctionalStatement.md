# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The ordinary two-block Jacquet integral as a nonzero Whittaker functional**

JPSS 1983, Section (4.6), printed pages 410-411. For blocks `τ_1, τ_2` of Whittaker
type and the opposite real twists `σ_1 = τ_1 ⊗ α^(-u)`, `σ_2 = τ_2 ⊗ α^u`, the source
shows that for `u ≫ 0` the integral (4.6.2) converges for every section of the lower
induction `σ_u`, and that the resulting function of `g` belongs to `W(σ_u; ψ̄)`. This
module states the integral realization behind that claim: for `u` above one bound,
every section is absolutely integrable, and the ordinary integrals are the coefficients
`g ↦ J(σ_u(g) f)` of one nonzero inverse-character Whittaker functional `J` on the
actual induced representation. It proves nothing, and it does not compare `J` with
other Whittaker functionals of `σ_u`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement` (def): JPSS 1983, Section (4.6), printed pages 410-411: for blocks `τ_1, τ_2` of full
  standard Whittaker type and supplied nonzero inverse-character functionals `ℓ_1, ℓ_2`,
  there is a real bound `C` such that for every real `u > C`, writing `σ_u` for the actual
  lower induction of `(τ_1 |det|^(-u), τ_2 |det|^u)` and `μ` for the product of the
  supplied self-dual Haar measure,

  * the raw integrand of (4.6.2) of every section is absolutely integrable at every
    ambient element, and
  * there is a nonzero `ψ⁻¹`-equivariant functional `J` on `σ_u` with
    `J(σ_u(g) f) = ∫ (ℓ_1 ⊗ ℓ_2)(f(u(x) g)) ψ(x_(m_0,0)) dμ(x)` for every section `f` and
    every `g`.
