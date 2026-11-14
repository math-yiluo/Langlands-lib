# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unconditional convergence of the JPSS Section 6.1 tensor integral**

This is the convergence assertion of the Proposition in JPSS Section 6.1,
printed pp.428–429, for formula (8). It uses the published special lower-block
model unchanged and quantifies over the entire algebraic tensor test space.
The large-positive-twist restriction concerns the separate induced-model
spanning assertion. This module defines an unproved proposition.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentRankModelConvergenceStatement` (def): JPSS Section 6.1, formula (8): every test tensor has an integrable scalar
  integrand at every ambient element, for every quasicharacter and every supplied
  self-dual scalar Haar measure, when the inner representation has full standard
  Whittaker type. The conclusion uses exactly the canonical p-adic model and its
  shared Haar measure. This definition supplies no convergence proof.
