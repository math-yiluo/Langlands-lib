# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockGammaDescentObjects`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockGammaDescentObjects` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockGammaDescentObjects`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockGammaDescentObjects` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Conditional representation packaging for gamma rank descent.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockEquivalence`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapStatement`
- `Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputStatement`
- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.Object` (structure): Actual representations of positive rank in a carrier universe closed under
  normalized induction, retaining all three full Whittaker-type conditions.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.family` (def): The original representations, with their ranks matched to `indices`.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.family_type` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.induced` (def): The actual canonical normalized induction, bundled with full type obtained
  from the explicit preservation premise.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.gamma` (def): A chosen certified unit. The analytic construction input is an explicit
  premise, rather than a claim of unconditional gamma existence.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.gamma_cert` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.certificate_swap` (theorem): Equal-rank exchange is supplied by its explicit analytic premise. In
  unequal ranks the larger-rank-first predicate gives exchange definitionally.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.gamma_swap` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.equality_of_certificates` (theorem): Uniqueness changes a certified finite product into an equality between the
  chosen units. This uses no analytic argument.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.dominant_eq` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.adjacent_eq` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.rankOne_eq` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.allRanks_eq` (theorem): The two-stage algebra is instantiated on actual full-type representations
  and certified units. Every analytic result remains an explicit premise.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.ofRepresentation` (def): Bundle an original full-type representation without changing its action.
- `Langlands.AllField.RankinSelberg.TwoBlockGammaDescent.certified` (theorem): Conditional all-rank multiplicativity for the target's arbitrary dependent
  ordered block family, using an actual induced-representation equivalence.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockGammaDescent.indices`, `Langlands.RankinSelberg.TwoBlockGammaDescent.indices_sum`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
