# The finite norm quotient A_K / N(L|K) A_L

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L | K` of abstract fields (closed subgroups `L ≤ K` of a group `G`, with `L` of finite index in `K`) and a `G`-module `A`, this file defines the norm subgroup `N(L|K) A_L` of the invariants `A_K` and the quotient `A_K / N(L|K) A_L`, the target of the finite reciprocity isomorphism. It then shows that the quotient of `A_K` by the norms from the maximal unramified extension `L̃` of `L` maps to it, so that the reciprocity construction descends to `A_K / N(L|K) A_L`.

## Main definitions and results

- `finiteNormSubgroup A K L hLK`: the image of the relative norm `A_L → A_K`.
- `FiniteNormQuotient A K L hLK`: the quotient `A_K / N(L|K) A_L`, a plain `def` with its own `AddCommGroup` instance and the identity equivalence `finiteNormQuotientConcreteEquiv` to the underlying `QuotientAddGroup`.
- `finiteNormClassHom`, `finiteNormClass`: the class map, with simp lemmas for zero, sums, differences and natural multiples; `finiteNormClass_eq_zero_iff` (a class vanishes exactly on norms), `finiteNormClass_surjective`, the eliminator `FiniteNormQuotient.induction_on`, and `finiteNormQuotientLift`, the factorisation of a homomorphism vanishing on norms.
- `finiteNormQuotient_degree_nsmul_eq_zero`: for a finite abstract extension `E`, the quotient is killed by the degree `[L : K]`, because the norm of an element of `A_K` is its multiple by the degree.
- `DegreeData.fieldAsMaximalUnramifiedIntermediate`: `L` regarded as a finite intermediate field of `L̃ | K`.
- `DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup`: the norm subgroup from `L̃`, which earlier files identify with the intersection of the norm groups of the finite intermediate fields of `L̃ | K`, lies in `N(L|K) A_L`; the proof takes the term of the intersection at `L` itself.
- `DegreeData.maximalUnramifiedToFiniteNormQuotient`: the resulting homomorphism `A_K / N(L̃|K) A_L̃ → A_K / N(L|K) A_L`, sending the class of `a` to the class of `a` (simp lemma `..._maximalUnramifiedNormClass`).

## Watch for

- `FiniteNormQuotient` is deliberately not reducible; work through `finiteNormClass`, `induction_on`, the lift and the concrete equivalence rather than unfolding it.
- `A` is written additively, so "norm subgroup" and "multiple by the degree" correspond to multiplicative norms and powers in the field case.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `0a7f6058dd3cb44787ac7ddb16526163ee9eea7b445d394621d7369178d70825`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
