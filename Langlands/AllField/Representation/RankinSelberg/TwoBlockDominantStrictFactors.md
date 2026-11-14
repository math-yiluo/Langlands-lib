# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFactors`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictFactors` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFactors`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFactors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Strict-rank symmetric factors and the L bound on the real ray**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFactors`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictRational`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_strictTwoBlockRationalComparison` (theorem): Above one real bound, a nonzero ordinary Jacquet functional supplies the
  actual rational comparison uniformly in all compatible quotient measures.
  The independently owned analytic first-block statement is an explicit premise.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictFirstBlockSymmetricFactors` (def): The full symmetric certificates attached to the retained first-block
  monomial and polynomial pair.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictFirstBlockFactorCertificate.symmetricFactors` (theorem): No generator or epsilon data are replaced when a retained first-block
  certificate is upgraded to symmetric factors.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictTwoBlockSymmetricLBound` (def): The actual strictly dominant lower induction and both actual blocks have complete
  symmetric L certificates with the required divisibility direction.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictTwoBlockSymmetricLBound_of_rationalComparison` (theorem): Identify the retained first-block polynomials in both directions and apply
  the intrinsic bound to a certified whole-pair L polynomial.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_strictTwoBlockSymmetricLBound` (theorem): Complete symmetric L certificates satisfy the required bound for all
  sufficiently large real opposite twists of arbitrary Whittaker-type blocks.
  The independently owned first-block theorem remains an explicit premise.
