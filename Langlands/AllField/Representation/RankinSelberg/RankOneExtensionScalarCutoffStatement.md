# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)**

JPSS (1983), Lemma (5.5), formula (9) and its proof, printed 426–427: right
smearing by the one-coordinate transvection against a Schwartz–Bruhat weight
whose plus-sign Fourier transform is the cut-off inverse quasicharacter.
The small-neighborhood refinement replacing `a` by `1` inside the original
coefficient is derived, as explained in the paired Markdown. This module only
defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneExtensionScalarCutoffStatement` (def): For every open neighborhood `O` of `1`, there are a compact open set
  `U ⊆ O` of normalized absolute value one containing `1`, an actual
  Schwartz–Bruhat pair `κ, Φ` with `Φ = fourierIntegral ψ ν κ` everywhere,
  `Φ 0 = 0` and `Φ a = χ(a)⁻¹` on units in `U`, zero on other units, and one
  coefficient `f₁` in the same coefficient model as `f₂`. The coefficient `f₁`
  is the global right `κ`-smearing of `f₂` along
  `rankOneExtensionSmearingUnipotent t k`, it equals `Φ(a) f₂` on every embedded
  lower block `B(a)`, `U` is small enough that `f₂(B(a)) = f₂(B(1))` for
  `a ∈ U`, and hence `f₁(B(a))` is `χ(a)⁻¹ f₂(B(1))` on `U` and zero otherwise.
  This is a closed proposition definition, not a proof.
