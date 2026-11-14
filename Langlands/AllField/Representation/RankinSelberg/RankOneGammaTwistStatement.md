# All-field port of `Langlands.Representation.RankinSelberg.RankOneGammaTwistStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneGammaTwistStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneGammaTwistStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rank-one determinant twists of gamma certificates**

Twisting a representation `π` of `GL_(n+1)` by `χ ∘ det` and pairing it with
the trivial character of `GL_1` gives the same gamma certificate as pairing
the untwisted `π` with the rank-one character `χ ∘ det`. This is an internal
consequence of the JPSS (1983) integral and dual-transform definitions, not a
numbered theorem of that paper. This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneGammaTwistStatement` (def): For every representation `π` of `GL_(n+1)(F)` and every character `χ` of
  `Fˣ`, a rational function `G` certifies `γ(s, (π ⊗ χ ∘ det) × 1, ψ)` exactly
  when it certifies `γ(s, π × χ, ψ)`, with the same additive character `ψ` and
  additive Haar measure `ν`. Both sides are the existing full p-adic gamma
  relation: the rank-one test is the smaller rank, so each side is the pair
  relation with `π` (twisted or not) first.
