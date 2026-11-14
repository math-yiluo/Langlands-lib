# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalytic` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalytic` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The deformed Whittaker coefficients of flat sections are entire**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalysis`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationFlat`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.FlatCoefficientDifferentiable` (def): The analytic conclusion: for inverse-character functionals `J_u` on `ρ_u` that agree
  with JPSS (4.6.2) at the identity on the compact-radical sections, where the latter
  together with the character relations span `ρ_u`, every coefficient
  `u ↦ J_u(ρ_u(g) f_u)` of a flat family is entire.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.unipotentExhaustion` (def): A chosen increasing exhaustion of the upper unipotent group by compact open subgroups.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isCompact_unipotentExhaustion` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.monotone_unipotentExhaustion` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_mem_unipotentExhaustion` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.sectionEval_sum` (theorem): Evaluation of a finite sum of sections.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.deformedAverage` (def): The `ψ⁻¹`-twisted average of `ρ_u` over the `k`-th subgroup of the exhaustion.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.functional_deformedAverage` (theorem): Inverse-character functionals are unchanged by the averages.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_deformedAverage_mem` (theorem): If the character relations and the compact-radical sections span `ρ_u`, every section
  is averaged into the compact-radical sections far enough along the exhaustion.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.inducedRep_flatSection_of_mem` (theorem): A translate `ρ_u(g) f_u` of a flat section is fixed by every `n` whose conjugate
  `g⁻¹ n g` lies in the uniform stabilizer of `f`.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.inv_smul_inducedRep_flatSection_of_mem` (theorem): The twisted form of `inducedRep_flatSection_of_mem` for a trivial character value.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_deformedAverage_formula` (theorem): The average of a translated flat family is a finite exponential sum in `u` with
  `u`-independent coefficients: `(P_k ρ_u(g) f_u)(y) = ∑_i κ(y d_i)^u a_i f(y d_i)`. The
  coset representatives come from one finite-index subgroup of the `k`-th subgroup which
  fixes `ρ_u(g) f_u` for every `u` and lies in the kernel of the character.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.flatCoefficientDifferentiable` (theorem): The deformed Whittaker coefficients of flat sections are entire.
