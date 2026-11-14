# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityProof`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDivisibilityProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Restricted rank-one extension reverse L-divisibility**

The closed upper-induction form of JPSS Lemma 5.5, assembled from the
published strict span comparison, actual lower-to-upper factor transport,
full normalized Whittaker type and symmetric polynomial existence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionFactorTransport`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonProof`
- `Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionUpper_whittakerType_of_normalizedProduct` (theorem): Conditional preservation specialized to the exact upper block family.
  The dependent-data transport follows the published two-block assembly pattern;
  no multiplicativity assertion is used.
- `Langlands.AllField.RankinSelberg.rankOneExtension_certificates_of_inputs` (theorem): Construct the actual two certificates conditionally on the separately
  owned full-type and common-existence statements at the needed universes.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLDivisibility_of_certificates_and_span` (theorem): The algebraic assembly, conditional on the actual certificates and the
  strict base-to-lower-induced span comparison.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLDivisibility_of_inputs` (theorem): Assemble the exact parent proposition from full type, common existence
  at both carrier universes, and the strict span comparison.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLDivisibility` (theorem): JPSS Lemma 5.5 in its original strict rank range, for the actual ordered
  upper normalized induction `(χlift, σ₁)`. Both certified polynomials and
  the reverse divisibility are conclusions.
