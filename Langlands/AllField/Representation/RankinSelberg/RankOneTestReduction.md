# All-field port of `Langlands.Representation.RankinSelberg.RankOneTestReduction`

`Langlands.AllField.Representation.RankinSelberg.RankOneTestReduction` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneTestReduction`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneTestReduction` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Reduction of rank-one tests to the trivial scalar test**

## Imports from the port

- `Langlands.AllField.Representation.Induction.NormalizedProductCharacterTwist`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.quasicharacter_isOpen_ker` (theorem): A continuous complex character of the scalar group of a supplied p-adic
  realization has open kernel.
- `Langlands.AllField.RankinSelberg.quasicharacterSmoothCharacter` (def): The same scalar character, packaged with the open kernel needed for actual
  smooth normalized induction.
- `Langlands.AllField.RankinSelberg.isOfWhittakerType_quasicharacter_twist_iff` (theorem): Continuous determinant twists retain all three parts of full Whittaker
  type, on an arbitrary carrier.
- `Langlands.AllField.RankinSelberg.isPadicPairLPolynomial_twist` (theorem): Opposite determinant twists preserve the quotient-measure existence
  witness and the polynomial certificate for every compatible measure.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_twist` (theorem): The same full L-certificate transport for both rank orders, with the
  original order retained in the equal-rank branch.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_rankOne_test_twist` (theorem): Move a scalar test character to a determinant twist of the other
  representation, without changing the full symmetric L certificate.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricGammaFactor_rankOne_test_twist` (theorem): The analogous gamma transport with the scalar test first. Full type is
  needed only for the equal-rank exchange; positive rank uses the larger-first
  definition directly.
- `Langlands.AllField.RankinSelberg.twoBlockGammaRankOne_of_trivial_test` (theorem): A two-block gamma theorem for the trivial scalar test suffices for the
  published arbitrary-carrier rank-one target. The analytic premise is explicit.
- `Langlands.AllField.RankinSelberg.twoBlockLRankOne_of_trivial_test` (theorem): A two-block L theorem for the trivial scalar test suffices for the
  published arbitrary-carrier target, preserving the exact polynomial identity.
