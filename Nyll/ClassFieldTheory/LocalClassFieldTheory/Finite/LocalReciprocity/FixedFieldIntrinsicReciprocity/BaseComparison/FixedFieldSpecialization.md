# Extension subgroups and inertia for finite fixed fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldSpecialization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field and `H` a finite abstract field of `Gal(K^sep/K)`, that is, a closed subgroup of finite index, with fixed field `F`. Let `J ≤ H` be a closed subgroup, normal and of finite index in `H`, with relative fixed field `E`, a finite Galois extension of `F`. Let `e` be an `F`-algebra isomorphism from the separable closure of `F` to `K^sep`. The file compares the intrinsic description of `E/F` inside `F^sep`, through the embedding `e⁻¹` of `E`, with its description by `J ≤ H` inside `Gal(K^sep/K)`. The comparison uses the isomorphism `φ : Gal(F^sep/F) ≃* H`, conjugation by `e`.

## Main results

- `intrinsicExtensionSubgroup_iff_ambientFixedField`: `τ ∈ Gal(F^sep/F)` lies in the intrinsic extension subgroup of `E/F` if and only if `φ(τ)` lies in the extension subgroup of `J ≤ H`. The proof uses the compatibility of the two quotient isomorphisms with `Gal(E/F)` (`fixedFieldQuotientEquiv_mk_compatibility`) and their injectivity.
- `intrinsicExtensionInertia_iff_ambientFixedField`: for `K` a nonarchimedean local field, the same equivalence for extension inertia, taken for `localResidueDatum F` and `localResidueDatum K`. The proof combines the previous result with the equality of normalized degrees under `φ` (`intrinsicBase_normalizedDegree_eq_ambientFixedField`); field inertia is the kernel of the normalized degree.
- `intrinsicFixedFieldSeparableClosureEquiv K H`: the type of the isomorphisms `e`.
- `intrinsicFixedFieldFrobeniusQuotient K H J hJH e`: the quotient of `Gal(F^sep/F)` by the extension inertia of the intrinsic presentation of `E/F`.

A private lemma says that elements with equal images under two homomorphisms lie in their kernels simultaneously.

## Points to watch

- In the local statements, `F` carries the library's spectral-norm local-field structure on a finite extension of `K`, not a structure given in advance.
- `intrinsicFixedFieldFrobeniusQuotient` is only the quotient by inertia; no Frobenius element is chosen in it.
- Extension subgroups and inertia are the library's class-formation notions (`extensionSubgroup`, `extensionInertiaWithin`), not Mathlib's.
- The local statements take `K : Type`, the purely Galois-theoretic one `K : Type u`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/FixedFieldSpecialization.lean`: the Lean file is the source byte for byte (SHA-256 `a592f277ce8bd7ac92902a040602e29bc85b5321e9707268380e6339d8892c8b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
