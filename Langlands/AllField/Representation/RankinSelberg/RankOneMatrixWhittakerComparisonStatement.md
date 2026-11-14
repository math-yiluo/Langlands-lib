# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rank-one JPSS `I₁ = I₃`: character zeta values versus matrix–Whittaker integrals**

The comparison `I₁ = I₃` of JPSS (1983), Section 5.2, printed 420–421, as an
equality of Laurent submodules of `RationalFunctions`, for every full
Whittaker-type representation of actual rank `n + 1` and every nonzero
standard Whittaker functional. This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneMatrixWhittakerComparisonStatement` (def): JPSS (1983) Section 5.2, `I₁ = I₃` (from JPS 1979 Theorem 4.3 and Remark 4.2
  when `n > 0`, and directly from the Tate/equal-rank integral when `n = 0`).
  For `σ` of full Whittaker type on `GL_(n+1)` and a nonzero standard functional `ℓ`,
  the Laurent span of the rank-one character zeta values of `σ × 1` equals the
  Laurent span of the shifted Godement–Jacquet integrals of the coefficient model
  of `ℓ`. Every compatible quotient measure on `N₁ \ GL₁` is quantified.
