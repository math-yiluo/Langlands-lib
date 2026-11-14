# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionProof`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCompactSectionProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the normalized compact sections for the strict rank-one extension**

The section is the published double-coset section `P̄ · 1 · K` of the lower
induction, for a compact open subgroup `K` with block Iwahori factorization for the
lower shape, and value `vol(L)⁻¹ (w ⊗ 1)` at the identity, where `L = {y | u(y) ∈ K}`.
The test function is `vol(L)⁻¹ 1_L`. Since `P̄` meets the upper radical trivially,
the factorization `K = (K ∩ N̄) (K ∩ M) (K ∩ N)` identifies the section on the whole
upper cell and its support.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.isSmooth_oppositeInducing` (theorem): The inflated and twisted inducing representation of a smooth Levi representation
  is smooth on the lower parabolic.
- `Langlands.AllField.RankinSelberg.exists_rankOneExtensionCellSection` (theorem): The cell-section construction for an arbitrary smooth representation `ρ` of the
  lower parabolic of the lower shape and an arbitrary vector `x₀`.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLowerFamily_isSmooth` (theorem): The two block factors `(σ, χ)` of the lower induction are smooth.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLowerInducing_isSmooth` (theorem): The inducing representation of the lower induction of `(σ, χ)` is smooth.
- `Langlands.AllField.RankinSelberg.rankOneExtensionCompactSection` (theorem): JPSS (1983), Lemma (5.5), formulas (5)–(7): normalized compact sections of the actual
  lower induction of `(σ, χ)`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneExtensionCellCoordinate`, `Langlands.RankinSelberg.rankOneExtensionLowerShape_index_zero`, `Langlands.RankinSelberg.rankOneExtensionLowerShape_index_one`, `Langlands.RankinSelberg.rankOneExtensionCellCoordinate_upperCell`, `Langlands.RankinSelberg.rankOneExtensionUpperCell_index_one_zero`, `Langlands.RankinSelberg.rankOneExtensionUpperCell_index_zero_zero`, `Langlands.RankinSelberg.rankOneExtensionUpperCell_index_one_one`, `Langlands.RankinSelberg.rankOneExtensionUpperCell_mem_unipotentSubgroup`, `Langlands.RankinSelberg.eq_rankOneExtensionUpperCell_of_mem_unipotentSubgroup`, `Langlands.RankinSelberg.continuous_rankOneExtensionCellCoordinate`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
