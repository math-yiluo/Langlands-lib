# The field fixed by a Frobenius lift

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract construction of the reciprocity map, a Frobenius lift `σ` is an element of `G_K / I_L = G(L̃ | K)` (with `L̃` the maximal unramified extension of `L`), and `Γ` is the closed subgroup it generates. An earlier file treats `Γ` group-theoretically; this file builds the actual abstract field `Σ` fixed by `σ`, as the closed subgroup `G_Σ` of `G` obtained as the inverse image of `Γ` under `G_K → G_K / I_L`, and computes its invariants. Throughout, `K` is a finite residue abstract field for a degree map `D`, and `L ≤ K` is closed with `G_L` normal in `G_K`.

## Main definitions and results

- `DegreeData.frobeniusFixedSubgroupWithin` (inside `G_K`) and `DegreeData.frobeniusFixedField` (as a closed subgroup of `G`), with membership lemmas, closedness, `frobeniusFixedField_le` (`Σ ⊇ K`) and `extensionSubgroup_frobeniusFixedField`.
- `fieldInertia_le_frobeniusFixedField`: `I_L ≤ G_Σ`.
- `frobeniusFixedField_finite` and `frobeniusFixedFiniteExtension`: for `G` compact Hausdorff and `L | K` finite, `Σ | K` is finite; `frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_one` gives `[Σ : K] ≤ [L : K]` when the Frobenius exponent of `σ` is `1`.
- `frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin`: `G_Σ ∩ I_K = I_L`, and `frobeniusFixedField_fieldInertia`: `I_Σ = I_L`, the subgroup form of `Σ̃ = L̃`.
- `frobeniusFixedField_residueDegreeOverBase`: the relative residue degree `f(Σ|K)` equals the Frobenius exponent `d_K(σ)`; `frobeniusFixedResidueField` equips `Σ` with its finite residue data, and `frobeniusFixedResidueField_residueDegree` gives `f_Σ = d_K(σ) · f_K`.
- `frobeniusFixedFieldToClosure`, surjective with kernel `I_Σ`, and `frobeniusFixedFieldQuotientEquiv : G_Σ / I_Σ ≃* Γ`.
- `frobeniusFixedField_normalizedDegree_compatibility` and `frobeniusFixedFieldQuotientEquiv_degree`: the normalized degree defined on `Γ` agrees with the intrinsic normalized degree of `Σ`.
- `frobeniusFixedField_frobenius_eq_inClosure`: under this identification, the Frobenius of `Σ` is `σ`.

## Proofs

`G_Σ ∩ I_K = I_L` and the Frobenius identification both rest on injectivity of the normalized degree on `Γ`, from the earlier Frobenius fixed-field theorem. The residue-degree formula computes the relative index of degree images, using that the image of `Γ` under the normalized degree is `d_K(σ) · Ẑ`; the remaining identities cancel residue degrees, multiplication by a positive integer on `Ẑ` being injective.

## Watch for

- The statements about `I_Σ`, the quotient equivalence and the Frobenius, and the index bound for exponent one, need `G` compact, Hausdorff and totally disconnected; finiteness of `Σ | K` and the relative formula `f(Σ|K) = d_K(σ)` need `L | K` finite, while the absolute formula `f_Σ = d_K(σ) · f_K` does not.
- The "Frobenius exponent" is the normalized degree `d_K(σ)`, a positive natural number.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`: the Lean file is the source byte for byte (SHA-256 `89dba232048ae4f3a1a483da54951e9db276c8f655709668d8604e461c621dce`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
