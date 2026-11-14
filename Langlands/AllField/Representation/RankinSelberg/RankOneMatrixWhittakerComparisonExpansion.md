# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Matrix integrals of a Whittaker model as rank-one integrals**

For `σ` smooth on `GL_(m+2)`, a standard functional `ℓ`, a matrix test function `Φ` and
a model function `W`, there is one model function `W'` such that for every `s` with
absolutely convergent shifted matrix integral `Z(Φ, s + (m+1)/2, W)`, the rank-one
integral `Ψ(s, W')` converges absolutely and the two agree. Hence the shifted
matrix values of the model lie in `rankOneModelValues`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnfolding`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonCutoff`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unitsCongruence` (def): The principal units of level `M`: `x - 1` and `x⁻¹ - 1` lie in `πᴹ O`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_unitsCongruence` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.diagonalUnits_mem_congruenceGroup` (theorem): A diagonal matrix of principal units lies in the congruence subgroup.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.torusCoord_one_mem` (theorem): The torus coordinate of a principal-unit tail is a principal-unit vector.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_model_congruence` (theorem): A model function of a smooth representation is right invariant under a congruence
  subgroup.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.hProduct` (def): The product `J(y) W(y)` of the unipotent transform and the model function.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.hFamily` (def): The family `(a, k) ↦ (g ↦ J(D(g,a) k) W(D(g,a) k))`, cut off to integral `k`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.diagPoint_mul` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.hProduct_mul_right` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.outerCongruence` (def): The open subgroup `(U_M)ⁿ × K_M` of the outer parameters.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_outerCongruence` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.one_mem_outerCongruence` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.hFamily_mul_right` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isCompact_integralSet` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isCompact_unitBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_compact_hFamily` (theorem): The family vanishes outside a compact set of outer parameters.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup_anti` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.hFamily_finite` (theorem): For smooth `σ`, the family takes finitely many values and has measurable fibres.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_model_hFamily` (theorem): Every value of the family is the restriction to `diag(det g, 1, …, 1)` of a model
  function: the corner transform is a Schwartz–Bruhat function of `det g`, and the Fourier
  cutoff absorbs it into a right translate of `W`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.weight_smul_determinantWeight` (theorem): The density identity `|det g|⁻ⁿ · |det g|^(s + n/2) = |det g|^(s - n/2)`, `n = m + 1`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.glModelFunction_sum` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_rankOneModel_of_matrix` (theorem): **Expansion of the matrix integral.** For smooth `σ`, a matrix test function `Φ` and a
  model vector `w`, one model vector `w'` (independent of `s`) satisfies: whenever the shifted
  matrix integral `Z(Φ, s + (m+1)/2, W)` converges absolutely, the rank-one integral
  `Ψ(s, W')` converges absolutely and equals it.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues` (theorem): **Right ⊆ Left.** The shifted matrix values of the model of `ℓ` lie in the rank-one
  model values.
