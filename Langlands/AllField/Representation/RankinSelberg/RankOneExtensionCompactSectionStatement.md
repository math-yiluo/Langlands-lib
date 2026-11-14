# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized compact sections for the strict rank-one extension**

JPSS (1983), Lemma (5.5), printed 424–425, formulas (5)–(7): an actual section of
the lower induction of `(σ, χ)`, supported in the lower opposite parabolic times the
complementary upper cell, whose restriction to that cell is a normalized compact test
function times a fixed pure tensor, with the test function supported where the
supplied vector of `π` is fixed. This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneExtensionCompactSectionStatement` (def): The normalized compact-section construction of the early JPSS Lemma (5.5)
  argument, in the strict rank range `t + 3 ≤ r + 1` with `r + 1 = (1 + (t + 1)) + (k + 1)`.
  For every open neighbourhood `O` of zero in the row space `Fin (t + 1) → F`, there are a
  Schwartz–Bruhat function `φ` supported in `O` with integral one for the supplied
  self-dual row measure, and an actual section `f` of the published lower induction of
  `(σ, χ)` such that `f (u(y)) = φ y • (w ⊗ 1)` on the upper cell, `f` vanishes off
  `P̄ · u(supp φ)`, and every `y ∈ supp φ` fixes `v` under `π (diag(u(y), I_(k+1)))`.
