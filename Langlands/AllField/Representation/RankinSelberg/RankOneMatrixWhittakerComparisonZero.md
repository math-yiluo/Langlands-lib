# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rank-one `I₁ = I₃` at actual rank one**

The `n = 0` branch of `RankOneMatrixWhittakerComparisonStatement`: a GL₁
equal-rank/Tate bridge. The subgroup `N₁` is trivial, so every compatible
quotient measure is the transported normalized Haar measure of `GL₁`; the
inverse Whittaker functions of the trivial character are the constants; vector
and `1 × 1` matrix test functions correspond through the last row; and the
complex shift `jpssShift 0` vanishes.

The file also proves two facts used by both branches: a nonzero standard
functional of a representation of Whittaker type gives the whole all-functional
Whittaker set, and at rank one every linear form is an inverse-character
functional.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneMatrixWhittakerComparison_zero` (theorem): The `n = 0` case of `RankOneMatrixWhittakerComparisonStatement`, in exactly the
  form of the statement's body at `n = 0`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.exists_eq_smul_of_linearEquiv_complex`, `Langlands.RankinSelberg.whittakerSet_eq_of_isOfWhittakerType`, `Langlands.RankinSelberg.glInverseFunctionals_rankOne`, `Langlands.RankinSelberg.mem_inverseWhittakerSet_rankOneCharacter_one_iff`, `Langlands.RankinSelberg.schwartzBruhatComap`, `Langlands.RankinSelberg.schwartzBruhatComap_apply`, `Langlands.RankinSelberg.oneByOneRow`, `Langlands.RankinSelberg.lastRow_eq_oneByOneRow`, `Langlands.RankinSelberg.constInverseWhittaker`, `Langlands.RankinSelberg.constInverseWhittaker_apply`, `Langlands.RankinSelberg.eq_rankOneQuotientHaar_of_isCompatible`, `Langlands.RankinSelberg.equalRankIntegral_rankOneQuotientHaar`, `Langlands.RankinSelberg.equalRankConverges_rankOneQuotientHaar_iff`, `Langlands.RankinSelberg.characterZetaValues_one_zero_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
