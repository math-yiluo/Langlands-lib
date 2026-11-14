# All-field port of `Langlands.Representation.Whittaker.InducedFiniteTypeProof`

`Langlands.AllField.Representation.Whittaker.InducedFiniteTypeProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.InducedFiniteTypeProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. The original transports a supplied realization to the canonical one (`topology_eq_canonical…`); in the port this transport is unnecessary and is omitted.

Source: the original module `Langlands.Representation.Whittaker.InducedFiniteTypeProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Proof route

The original rewrites the topology of the finite-length result `glAdmissibleFiniteLength` to the canonical one; the port applies the all-field result at `(⟨⟩ : LocalFieldData F)`, whose topology is the ambient one, so no rewriting is needed.

## Imports from the port

- `Langlands.AllField.Representation.Classification.FiniteLengthProof`
- `Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof`
- `Langlands.AllField.Representation.Induction.BlockCharacterAbsorption`
- `Langlands.AllField.Representation.Induction.SingleBlockSupplement`
- `Langlands.AllField.Representation.Whittaker.InducedStatement`

## Declarations

- `Langlands.AllField.inducedFiniteType` (theorem): Actual upper-parabolic smooth induction preserves finite type for
  admissible finite-type complex GL block representations.
