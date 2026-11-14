# All-field port of `Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof`

`Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the reduction of full rank-one Whittaker type to a quasicharacter**

The algebraic dual of the carrier is the whole rank-one functional space, hence
linearly equivalent to `ℂ`. A functional corresponding to `1` is then a linear
equivalence of the carrier with `ℂ`, and transporting the action gives a
character. A smooth vector supplies an open kernel, hence continuity.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneCharacterReduction` (theorem): The arbitrary-carrier reduction of full rank-one Whittaker type to the
  scalar representation of a continuous quasicharacter.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.dual_symm_one_bijective`, `Langlands.RankinSelberg.eq_coord_smul_symm_one`, `Langlands.RankinSelberg.transportedScalar`, `Langlands.RankinSelberg.transportedScalar_apply`, `Langlands.RankinSelberg.scalar_determinant_rankOne`, `Langlands.RankinSelberg.exists_quasicharacter_equiv_of_isOfWhittakerType`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
