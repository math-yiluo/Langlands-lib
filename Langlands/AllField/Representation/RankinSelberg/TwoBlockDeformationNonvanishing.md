# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationNonvanishing` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**A section of the two-block induction with nonzero Jacquet value at the identity**

Let `σ_1, σ_2` be smooth representations of `GL_(m_1+1)(F)` and `GL_(m_2+1)(F)` and
let `ℓ_1, ℓ_2` be nonzero linear functionals on their spaces. This module constructs a
section `f` of the actual lower induction `I(σ_1 ⊗ σ_2)` such that `x ↦ f(u(x))` has
compact support on the upper radical and the Jacquet integral
`J(f)(1) = ∫ ⟨f(u(x)), ℓ_1 ⊗ ℓ_2⟩ ψ(x_(m_1,0)) dx` of JPSS (4.6.2) is nonzero.

The section is supported on `Q̄ K`, for a compact open subgroup `K` with a block Iwahori
factorization `K = (K ∩ Ū)(K ∩ M)(K ∩ U)`, with value `v_1 ⊗ v_2` at the identity, where
`ℓ_i(v_i) ≠ 0`. Since `Q̄ ∩ U = 1`, its restriction to the upper radical is
`u(x) ↦ (v_1 ⊗ v_2) 1[u(x) ∈ K]`, so `J(f)(1) = ℓ_1(v_1) ℓ_2(v_2) μ{x : u(x) ∈ K}`.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.character_eq_one_mem_nhds` (theorem): A unitary additive character of a p-adic field is trivial near `0`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_section_jacquetFunction_one_ne_zero` (theorem): For smooth blocks and nonzero functionals `ℓ_i`, some section of the actual lower
  induction has compactly supported restriction to the upper radical and nonzero
  Jacquet value `J(f)(1)`, for every Borel additive Haar measure on the rectangular
  coordinates.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isSmooth_twoBlockDeformedBlocks` (theorem): The deformed blocks `σ_u` of blocks of full standard Whittaker type are smooth.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_deformed_section_jacquetFunction_one_ne_zero` (theorem): For blocks of full standard Whittaker type, every deformation `ρ_u` has a section
  with compactly supported restriction to the upper radical and nonzero Jacquet value at
  the identity, for any nonzero functionals `ℓ_i` on the block spaces.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDeformation.mem_of_mem_unipotentSubgroup_of_mul_inv_mem`, `Langlands.RankinSelberg.TwoBlockDeformation.upperRadical_mem_unipotentSubgroup`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
