# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankCertifiedRealRay`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankCertifiedRealRay` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankCertifiedRealRay`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankCertifiedRealRay` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankRealRayClearing`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.corankOneCoefficient_denominatorBound_of_certificate` (theorem): A complete induced L certificate and its exact polynomial divisibility
  bound each actual corank coefficient, for the supplied compatible measure.
- `Langlands.AllField.RankinSelberg.Padic.SecondBlockCorankRealRayCertificates` (def): Complete induced certificates with the fixed rescaled block product on
  one real ray. The certificates and polynomial relation remain explicit.
- `Langlands.AllField.RankinSelberg.Padic.secondBlock_realRayDenominatorBound_of_certificates` (theorem): Complete certificates and exact polynomial divisibility supply the
  actual reciprocal-span bound for every actual coefficient on the same ray.
- `Langlands.AllField.RankinSelberg.Padic.secondBlock_realRayClearing_of_certificates` (theorem): Published scalar spectral uniqueness converts certified actual
  real-ray polynomial divisibility to formal coefficient clearing.
