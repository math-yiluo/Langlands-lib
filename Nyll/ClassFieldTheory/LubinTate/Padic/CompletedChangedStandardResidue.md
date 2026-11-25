# Residue fields of the completed standard–changed compositum

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let u be a unit of ℤ_p, D the changed-uniformizer fixed field and M the standard–changed compositum at level n, both finite extensions of ℚ_p inside the completed Lubin–Tate level E. The file gives D and M their local-field structure, shows that D has residue field of p elements, so the residue arithmetic Frobenius of M/D is the p-th power map, and builds residue-field embeddings of D and M into the residue field of E. It supplies the residue comparison used to identify the relative Artin candidate with inverse arithmetic Frobenius.

## Main results

- `padicChangedUniformizerLevelResidueField_card`: the n-th standard Lubin–Tate level for the changed uniformizer has residue field of cardinality p (it is totally ramified: the fundamental identity with ramification index equal to the degree forces residue degree 1).
- `padicCompletedChangedUniformizerFixedField_residueField_card`: D, with its spectral valuation, also has residue field of cardinality p.
- `padicCompletedStandardChangedCompositum_residueArithmeticFrobenius_apply`: the residue arithmetic Frobenius of M/D is x ↦ x^p.
- `padicCompletedChangedFieldResidueEmbedding`, `padicCompletedStandardChangedCompositumResidueEmbedding`: ring maps from the residue fields of D and of M to that of E; the second is injective (`..._injective`).
- Instances: M is finite and Galois over D; D and M carry the spectral norm, valuative relation and local-field structure induced from ℚ_p; the valuation of M extends that of D; the valuation ring of M is the integral closure of that of D (in two formulations).
- `padicCompletedStandardChangedCompositumResidueEmbedding_artinCandidate`: under the residue embedding of M, the residue action of the relative Artin candidate equals the residue action of the inverse of the completed Frobenius integer equivalence for u⁻¹ on E.

## Proofs

The cardinality for D is transported from the finite changed level through the isomorphism of the two fields, using uniqueness of the extension of the p-adic valuation to a finite separable extension in both directions and comparing cardinalities. The embeddings come from the same uniqueness: the valuation of E pulled back to D or M is equivalent to its own valuation.

## Watch for

- D and M carry the valuation induced by the finite-extension spectral norm over ℚ_p, not the restriction of the valuation of E; the comparison between the two is what the embeddings provide.
- Several statements begin with `let` bindings that install these structures, and hold only for them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedStandardResidue.lean`: the Lean file is the source byte for byte (SHA-256 `110f76b0abed4c66670ea109baccc577343865c5ea040a39920670ce8086bfbd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
