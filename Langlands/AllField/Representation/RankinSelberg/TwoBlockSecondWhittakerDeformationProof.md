# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the entire standard-character deformation on the second lower block**

Proof of `Langlands.AllField.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`.
The published first-block inverse-character theorem `twoBlockWhittakerDeformation`
is applied with the additive character `ψ.scale (-1)` and evaluated at `-u`. An
actual equivalence between the global twist by `|det|^u` of the first-block family
at `-u` and the second-block family at `u` is constructed on lower-induced sections,
and the coefficients are multiplied by `|det g|^u`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.determinantComplexPower_oppositeParabolic` (theorem): On the lower block parabolic, `|det|^u` is the product of the block powers
  `|det a_i|^u` of its Levi projection.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.ambient_mul_firstBlock_eq_secondBlock` (theorem): The ambient twist `|det|^u` combined with the first-block twist `|det|^(-u)`
  gives the second-block twist `|det|^u` on every lower parabolic element.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.ambientCharacter` (def): The smooth ambient character `|det|^u` of `GL_(t+1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.twistComparison` (def): The actual comparison of lower-induced representations
  `|det|^u ⊗ ρ'_(-u) ≅ ρ_u`, where `ρ'` is the published first-block family and `ρ`
  the second-block family: multiplication of sections by `|det|^u`, followed by the
  identity on the dependent tensor carrier.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.zeroComparison` (def): At parameter zero the two families are the same untwisted induction; this is the
  induced equivalence of the identity coordinates.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.exists_second_coefficient` (theorem): Every second-block coefficient at `u` comes from a first-block coefficient at `-u`
  multiplied by `|det g|^u`: transport of the functional and vector along
  `twistComparison`.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.secondCoefficient_of_firstCoefficient` (theorem): The second clause at `u`, from the first-block clause at `-u` for the inverse
  character of `ψ.scale (-1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.exists_level_twistedFamily` (theorem): Multiplying a family by `|det g|^u` and reversing the parameter keeps one common
  compact open right stabilizer: intersect with the kernel of `|det|`.
- `Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation.analyticAt_twistedFamily` (theorem): Multiplying a pointwise entire family by `|det g|^u` and reversing the parameter
  keeps it pointwise entire.
- `Langlands.AllField.RankinSelberg.twoBlockSecondWhittakerDeformation` (theorem): Entire standard-character deformation on the second lower-induced block, derived
  from the published first-block inverse-character theorem by character change,
  the parameter `-u` and the global twist `|det|^u`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockSecondDeformation.blockTensor_twist_apply`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.inducingEquivOfApply`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.equiv_apply_symm_apply_rep`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.equiv_symm_apply_apply_rep`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.functionalsCongr_symm_val_rep`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.functionalsCongr_val_rep`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.functionalsCongr_val_ne_zero`, `Langlands.RankinSelberg.TwoBlockSecondDeformation.functionalsCongr_symm_val_ne_zero`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
