# A finite class field candidate for a norm-open subgroup

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file carries out the constructive part of the surjectivity proof in the finite abelian classification of abstract class field theory. Let `A` be a `ℤ`-representation of `G`, `K` an abstract field and `H` a subgroup of `A_K` open for the norm topology. Then `H` contains the norm group `N_E` of a finite Galois extension `E | K`. Passing to `H / N_E`, transporting it through a given isomorphism `A_K / N_E ≃ G(E|K)^ab` and pulling back to `G(E|K)`, one gets a subgroup containing the commutator subgroup, whose fixed field is a finite abelian extension of `K`: the candidate class field of `H`.

## Main definitions and results

- `normOpenAddSubgroup_contains_finiteNormSubgroup`: a norm-open `H` contains `normSubgroup A E` for some finite Galois subextension `E`.
- `normQuotientSubgroup`: the image `H / N_E` in the finite norm quotient; `finiteNormClass_mem_normQuotientSubgroup_iff`: if `N_E ≤ H`, then `H` is the full inverse image of `H / N_E`.
- `reciprocityAbelianizedSubgroup` and `reciprocityAbelianizedClassHom`: transport through a given equivalence `rE`; `reciprocityClass_mem_abelianizedSubgroup_iff`: `a ∈ H` iff its class lies in the transported subgroup.
- `abelianizationPreimageSubgroup` and `commutator_le_abelianizationPreimageSubgroup`: the pullback of a subgroup of `Q^ab` to `Q` contains the commutator subgroup.
- `intermediateFiniteAbelianOfCommutatorLe`: the finite abelian intermediate extension fixed by a subgroup of `G(E|K)` containing the commutator.
- `reciprocityPreimageSubgroup`, `reciprocityClass_mem_preimageSubgroup_iff` and `candidateQuotient_eq_one_iff`: for `a ∈ A_K`, a representative of its transported class lies in the pulled-back subgroup, or is trivial in the corresponding quotient, exactly when `a ∈ H`.
- `classFieldCandidate`: the resulting finite abelian subextension; `classFieldCandidate_field` identifies it as the fixed field of the pulled-back subgroup.

## Points to watch

- The isomorphism `rE : A_K / N_E ≃ G(E|K)^ab` is an explicit argument, not constructed here; it is to be supplied later by finite reciprocity. Nothing about `rE` being the reciprocity map is assumed.
- The file does not prove that the norm group of the candidate equals `H`; it constructs the field and the preimage statements only.
- `reciprocityClass_mem_preimageSubgroup_iff` and `candidateQuotient_eq_one_iff` use a chosen representative (`Quotient.out`) of the class in the abelianization; the other membership statements are about the class itself.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean`: the Lean file is the source byte for byte (SHA-256 `3d9912105fd987c159fa451dfa5dfbc15fd458673f585b0ef137cf69518422e7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
