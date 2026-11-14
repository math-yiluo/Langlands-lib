# All-field port of `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityStatement`

`Langlands.AllField.Representation.GodementJacquet.ModelWhittakerRationalityStatement` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.ModelWhittakerRationalityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Convergence and rationality of each Whittaker matrix integral on the model**

JPSS (1983), Section (5.2), printed 420–421: for `σ` of Whittaker type acting on
its Whittaker model, every full-matrix integral
`Z(Φ, s, W) = ∫ Φ(g) W(g) |det g|^s dg` converges for `Re s` large and defines a
rational function of `q^(-s)`. The common g.c.d. asserted there is not part of
this proposition. This module only defines the proposition.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`

## Declarations

- `Langlands.AllField.GodementJacquet.ModelWhittakerRationalityStatement` (def): Every shifted full-matrix Whittaker integral on the actual coefficient model
  converges on some right half-plane and has a rational continuation in
  `q^(-s)`. For a representation `σ` of `GL_(n+1)` of Whittaker type for the
  standard character, possibly reducible, a nonzero standard Whittaker functional
  `ℓ`, any Schwartz–Bruhat function `Φ` on all square matrices and any function
  `W` of the coefficient image of `ℓ`, the integral
  `∫ Φ(g) W(g) |det g|^(s + n/2) dg` for the normalized Haar measure converges
  absolutely for `Re s > a` for some real `a`, and agrees there with a rational
  function of `q^(-s)`. Each half-plane may depend on `Φ` and `W`.
