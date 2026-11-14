# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional two-block normalized matrix functional equation**

The functional-equation part of Godement–Jacquet 1972, Theorem 3.4 (printed
pages 36–45), with two blocks, for split `GL` over a canonical p-adic field, in
the transpose Fourier convention of JPS 1979, printed page 177. The statement is
conditional: the block normalized matrix data are premises, and the blocks may
be reducible. This module only states the proposition.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`
- `Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement` (def): Godement–Jacquet 1972, Theorem 3.4 (printed page 36), functional-equation
  part, with two blocks. Let `σ i` be smooth admissible, not necessarily
  irreducible, representations of `GL_(m i + 1)(F)` with scalar central
  quasicharacters `ω i`, let `ψ` be a nontrivial additive character and `ν` a
  Haar measure self-dual for `ψ`. If each block has normalized matrix
  functional-equation data `(P i, PDual i, c i, a i)` for `ψ` and `ν`, then the
  actual normalized induction of `(σ 0, σ 1)` to `GL_(t+1)(F)` has normalized
  matrix functional-equation data with the products of the polynomials, the
  product of the units and the sum of the exponents, for the same `ψ` and `ν`.
