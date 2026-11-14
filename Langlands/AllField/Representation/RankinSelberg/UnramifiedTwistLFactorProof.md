# All-field port of `Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof`

`Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistLFactorProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.isPadicPairLPolynomial_unramified_of_transport` (theorem): Transport preserves the supplied compatible measure's existence and works
  for every compatible quotient measure in the p-adic relation.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_unramified_of_transport` (theorem): Rank-order symmetry turns the ordered-pair result into both twist relations.
- `Langlands.AllField.RankinSelberg.unramifiedTwistLFactor_of_transport` (theorem): Assemble the target from continuation and normalized-generator transport.
- `Langlands.AllField.RankinSelberg.unramifiedTwistLFactor` (theorem): Twisting either member by the supplied unramified character transports the
  certified L-polynomial by `X ↦ q^(-u) * X`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.isPairLPolynomial_unramified_of_transport`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
