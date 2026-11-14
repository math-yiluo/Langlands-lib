# All-field port of `Langlands.Representation.Induction.BlockCharacterAbsorption`

`Langlands.AllField.Representation.Induction.BlockCharacterAbsorption` is the all-field port of the Library module `Langlands.Representation.Induction.BlockCharacterAbsorption`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.BlockCharacterAbsorption` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Absorbing the normalizing character into the block factors**

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Induction.Equivalences`

## Declarations

- `Langlands.LocalFieldData.blockHalfModulus` (def): The positive half Levi modulus restricted to the actual `i`th block.
- `Langlands.LocalFieldData.blockInverseHalfModulus` (def): The inverse half character on the actual `i`th block.
- `Langlands.LocalFieldData.blockHalfCharacter` (def): Coordinate restriction carries its open-kernel certificate.
- `Langlands.LocalFieldData.blockInverseHalfCharacter` (def): Inverting the coordinate restriction retains its open-kernel certificate.
- `Langlands.LocalFieldData.blockHalfCharacter_toMonoidHom` (theorem).
- `Langlands.LocalFieldData.blockInverseHalfCharacter_toMonoidHom` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_blockHalfModulus` (theorem).
- `Langlands.LocalFieldData.blockHalfModulus_apply` (theorem).
- `Langlands.LocalFieldData.blockInverseHalfModulus_apply` (theorem).
- `Langlands.LocalFieldData.blockHalfModulus_upperUnipotent` (theorem): The coordinate half modulus is one on the actual standard upper unipotent subgroup.
- `Langlands.LocalFieldData.blockHalfTwist` (def): Positive half twists of the supplied block representations, on their original carriers.
- `Langlands.LocalFieldData.blockInverseHalfTwist` (def): Inverse half twists of the supplied block representations.
- `Langlands.LocalFieldData.blockTensor_halfTwist` (theorem).
- `Langlands.LocalFieldData.blockTensor_inverseHalfTwist` (theorem).
- `Langlands.LocalFieldData.halfAbsorptionInducing_eq` (theorem): The actual parabolic covariance actions coincide after positive absorption.
- `Langlands.LocalFieldData.inverseHalfAbsorptionInducing_eq` (theorem): Inverse half twists cancel the normalization in the actual covariance action.
- `Langlands.LocalFieldData.halfAbsorptionInducingEquiv` (def): Identity on tensor values, regarded as an equivalence of the parabolic actions.
- `Langlands.LocalFieldData.inverseHalfAbsorptionInducingEquiv` (def): Identity on tensor values after inverse normalization.
- `Langlands.LocalFieldData.normalizedProductHalfAbsorptionEquiv` (def): Absorb positive normalization into the actual block factors.
- `Langlands.LocalFieldData.normalizedProductInverseHalfAbsorptionEquiv` (def): Normalize inverse-half-twisted factors to recover the original unnormalized induction.
- `Langlands.LocalFieldData.normalizedProductHalfAbsorptionEquiv_eval` (theorem): Both directions of positive absorption preserve every value of the induced function.
- `Langlands.LocalFieldData.normalizedProductHalfAbsorptionEquiv_symm_eval` (theorem).
- `Langlands.LocalFieldData.normalizedProductInverseHalfAbsorptionEquiv_eval` (theorem): Both directions of inverse absorption also preserve every function value.
- `Langlands.LocalFieldData.normalizedProductInverseHalfAbsorptionEquiv_symm_eval` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.Induction.SmoothCharacter.coordinate`, `Langlands.Induction.SmoothCharacter.coordinate_apply`, `Langlands.Induction.SmoothCharacter.inverse`, `Langlands.Induction.SmoothCharacter.inverse_apply`, `Langlands.Induction.SmoothCharacter.factorization`, `Langlands.Induction.SmoothCharacter.external_coordinate_twist`, `Langlands.PadicField.TopologicalData.isOpen_ker_blockInverseHalfModulus`, `Langlands.PadicField.TopologicalData.blockHalfModulus_factorization`, `Langlands.PadicField.TopologicalData.blockInverseHalfModulus_factorization`, `Langlands.PadicField.TopologicalData.blockInverseHalfModulus_upperUnipotent`, `Langlands.PadicField.TopologicalData.isAdmissible_blockHalfTwist_iff`, `Langlands.PadicField.TopologicalData.isAdmissible_blockInverseHalfTwist_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
