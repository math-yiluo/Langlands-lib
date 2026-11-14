# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLConditionalAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original, except for the rank-one high-ramification input described below. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional two-block L-polynomial rank descent**

Internal support for the two-stage descent of JPSS Section 7. The polynomial
relation preserves the powers of `X` permitted by the published target. Every
analytic input, including the separate equal-rank reverse comparison, remains
an explicit hypothesis. No closed multiplicativity theorem is asserted here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapStatement`
- `Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeStatement`
- `Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly.EqualRankReverseAt` (def): The fieldwise equal-rank reverse comparison required by the second
  descent. This internal predicate is an explicit input, with no proof asserted.
- `Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly.twoBlockLMultiplicativity_of_inputs_commonUniverse` (theorem): Packaging of the two actual descents as the full published target in a
  stable carrier universe. Every missing analytic result is still a premise.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLConditionalAssembly.PolynomialLDivides`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

## Deviation from the original: rank-one high-ramification input

This deviation was made by Worker 394 (Task 6539), after Worker 5220's port. In the
original, four declarations take the high-ramification hypothesis
`hram : WhittakerTypeHighlyRamifiedLVanishingStatement` (JPSS 1983, Proposition
(2.13), for all ranks): the private theorems `auxiliaryCharacter_exists`,
`twoBlockL_firstRankOne`, `twoBlockL_allRanks`, and the public
`twoBlockLMultiplicativity_of_inputs_commonUniverse`. In the port, `hram` has type
`Langlands.AllField.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneLVanishingStatement`
(at the same universes), the case of (2.13) in which the first member is a
representation of `GL_1`; see
[WhittakerTypeHighlyRamifiedRankOneStatement](WhittakerTypeHighlyRamifiedRankOneStatement.md).
The import `WhittakerTypeHighlyRamifiedStatement` is replaced by
`WhittakerTypeHighlyRamifiedRankOneStatement` accordingly.

The original uses `hram` only once, in `auxiliaryCharacter_exists`, as
`hram F ψ ν 0 (m i) (rankOneCharacter 1) (σ i) htrivial (hσ i)`, that is with first
rank `r = 0` and first member the trivial character of `GL_1`. The port makes the
same call without the argument `0`: `hram F ψ ν (m i) (rankOneCharacter 1) (σ i)
htrivial (hσ i)`, which has the same type. The rest of every proof is unchanged;
the three other declarations only pass `hram` on. The full proposition (2.13) implies
the rank-one one by taking `r = 0`, so the port's hypotheses are weaker than a
literal port's. The change matters in positive characteristic, where the proof route
of the Library gives only the rank-one case of (2.13) (see the linked Markdown).
