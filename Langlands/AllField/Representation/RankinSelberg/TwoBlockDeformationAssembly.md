# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Assembly of the entire deformation from the analytic input**

For every complex `u`, the JPSS integral (4.6.2) at the identity on the compact-radical
sections of `ρ_u` extends to an inverse-character Whittaker functional `J_u` of `ρ_u`.
Together with the relations it spans `ρ_u`. Given the analytic input
`FlatCoefficientDifferentiable` and uniqueness of inverse-character functionals, the family
`W_u(g) = c · J_u(ρ_u(g) f_u)` of flat sections `f_u` satisfies the four clauses of
`TwoBlockWhittakerDeformationStatement`. The analytic input is
`flatCoefficientDifferentiable`, so the closed proposition follows from
`NormalizedProductWhittakerTypeStatement` alone.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalytic`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationUniqueness`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_jacquetFunctional` (theorem): The JPSS integral at the identity on the compact-radical sections extends to an
  inverse-character Whittaker functional `J` of the actual lower induction. If some
  compact-radical section has nonzero integral and the inverse-character functionals are
  unique up to scalars, then `J ≠ 0` and the character relations together with the
  compact-radical sections span the whole induced space.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_deformation_of_functionals` (theorem): The four clauses from a family of nonzero inverse-character functionals `J_u` on `ρ_u`
  whose flat coefficients `u ↦ J_u(ρ_u(g) f_u)` are entire, provided every inverse-character
  functional on `ρ_0` is a multiple of `J_0`. The family is `W_u(g) = c · J_u(ρ_u(g) f_u)` with
  `ℓ₀ = c · J_0` and `f_u` the flat section through `v₀`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_deformation_of_differentiable` (theorem): JPSS (1983), Section (4.5), assembled from the analytic input: conditional on
  `NormalizedProductWhittakerTypeStatement` (uniqueness of inverse-character functionals on
  every `ρ_u`) and on `FlatCoefficientDifferentiable` (entire dependence of the flat
  coefficients), every coefficient `g ↦ ℓ₀(ρ₀(g) v₀)` of a nonzero inverse-character
  functional of `ρ₀` lies in an entire family with all four clauses of
  `TwoBlockWhittakerDeformationStatement`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of` (theorem): The closed target `TwoBlockWhittakerDeformationStatement`, conditional on
  `NormalizedProductWhittakerTypeStatement` and on `FlatCoefficientDifferentiable` for all
  blocks of full standard Whittaker type.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of_normalizedProduct` (theorem): The closed deformation proposition, conditional only on the full Whittaker type of the
  upper normalized products: the analytic input is `flatCoefficientDifferentiable`.
