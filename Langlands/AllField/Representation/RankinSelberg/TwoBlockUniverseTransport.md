# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUniverseTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Carrier-universe transport for two-block pair factors**

Internal equivalence transport only. The common-universe hypotheses below
remain analytic obligations; this module proves neither factor existence nor
multiplicativity without those hypotheses.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockEquivalence`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`

## Declarations

- `Langlands.LocalFieldData.normalizedProductInducedUniverseLiftEquiv` (def): Lift every carrier of the dependent block family through the actual
  normalized upper induction, keeping the entire ordered block shape fixed.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricGammaFactor_universeLift_iff` (theorem): Symmetric gamma certificates are unchanged under independent carrier lifts.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_universeLift_iff` (theorem): Symmetric L-polynomial certificates are unchanged under independent lifts.
- `Langlands.AllField.RankinSelberg.twoBlockGammaMultiplicativity_of_commonUniverse` (theorem): Conditional carrier transport from a common universe closed under
  normalized induction. This does not discharge the common-universe hypothesis.
- `Langlands.AllField.RankinSelberg.twoBlockLFactorMultiplicativity_of_commonUniverse` (theorem): Conditional carrier transport retaining the original certified
  L-polynomials and the unchanged equation `X^e * ∏ i, Pi i = Q * P`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.isOfWhittakerType_universeLift_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
