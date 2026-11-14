# All-field port of `Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement`

`Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Highly ramified L-vanishing for pairs of Whittaker type**

JPSS 1983, Proposition 2.13 (printed page 404), in the Whittaker-type scope
of Section 2.1. This proposition definition includes reducible representations
and both rank orders. The conclusion certifies the polynomial `1` in the
existing symmetric pair relation, including its compatible-measure existence
and universal measure quantifiers. No proof of the proposition is supplied.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`

## Declarations

- `Langlands.AllField.RankinSelberg.WhittakerTypeHighlyRamifiedLVanishingStatement` (def): JPSS 1983, Proposition 2.13: for any two representations of Whittaker type
  of positive ranks, sufficiently ramified determinant twists of the first have
  L-factor `1` against the second. The bound is uniform over all continuous
  quasicharacters whose multiplicative conductor is at least that bound.
  The supplied self-dual measure and additive character are arbitrary.
