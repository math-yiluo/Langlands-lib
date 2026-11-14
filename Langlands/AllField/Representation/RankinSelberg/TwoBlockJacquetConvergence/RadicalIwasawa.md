# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lower Iwasawa factorization of the upper radical**

For the upper radical `u(x) = [[1, x], [0, 1]]` of the two-block shape and a lower Iwasawa
factorization `u(x) = q k` with `q` in the lower block parabolic and `k ∈ GL_(t+1)(O)`, the
first diagonal block `A` of `q` has `|det A| = q_F^d` for a natural number `d`, the second
diagonal block has `|det| = q_F^(-d)`, both blocks and their inverses become integral after
multiplication by `ϖ^d`, and so does `x`.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationFlat`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.normalizedAbs_determinant_eq_one` (theorem): An element of `GL_(n+1)(O)` has determinant of normalized absolute value one.
- `Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_radical_factorization` (theorem): **Lower Iwasawa factorization of the upper radical.** Every `u(x)` factors as `q k` with
  `q` in the lower block parabolic and `k ∈ GL_(t+1)(O)` such that, for one natural number `d`,
  `ϖ^d x` is integral, both diagonal blocks of `q` are bounded by `d`, and their determinants
  have normalized absolute values `q_F^d` and `q_F^(-d)`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockConvergence.det_mem_of_forall_mem`, `Langlands.RankinSelberg.TwoBlockConvergence.adjugate_mem_of_forall_mem`, `Langlands.RankinSelberg.TwoBlockConvergence.val_eq_det_smul_adjugate_inv`, `Langlands.RankinSelberg.TwoBlockConvergence.determinant_oppositeParabolic`, `Langlands.RankinSelberg.TwoBlockConvergence.determinant_upperRadical`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
