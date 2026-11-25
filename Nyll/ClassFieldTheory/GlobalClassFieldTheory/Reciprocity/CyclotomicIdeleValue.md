# The normalized cyclotomic idele value

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let T = ℚ̃ be the cyclotomic ℤ̂-extension of ℚ, and for a number field K let f_K = [K ∩ ℚ̃ : ℚ] (`cyclotomicZHatIntersectionDegree K`, built in `CyclotomicZHatBaseChange`). The file defines the rational value v_ℚ : I_ℚ → ℤ̂ given by the Artin map to Gal(T/ℚ) ≅ ℤ̂, and the normalized value v_K = (1/f_K) · v_ℚ ∘ N on the ideles of K, where N is the idele norm from K to ℚ, after proving that v_ℚ ∘ N takes values in f_K ℤ̂.

## Main definitions and results

- `rationalCyclotomicZHatIdeleValue`: v_ℚ as a continuous homomorphism `IdeleGroup ℚ →ₜ* Multiplicative ZHat`. Its image is dense, already on norm-one ideles (`rationalCyclotomicZHatIdeleValue_normOne_denseRange`).
- `numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom` (simp): the infinite Artin map of K·T/K, restricted to T, is the rational Artin map of N(a).
- `cyclotomicZHatNormComposite K`: the composite v_ℚ ∘ N in additive notation. On a rational idele seen in I_K it is [K : ℚ] · v_ℚ (`..._baseIdeleInclusion`). `cyclotomicZHatIntersectionDegree_rat`: f_ℚ = 1.
- `finiteCyclotomicLayer_normArtin_range_eq_fixingSubgroup`: for a finite Galois layer E of T/ℚ, the Artin image of norms from K is the subgroup of Gal(E/ℚ) fixing K ∩ E.
- `rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup`: the Artin symbol of N(a) fixes K ∩ T. These symbols are dense in that fixing subgroup (`..._denseRange_in_intersection_fixingSubgroup`).
- `cyclotomicZHatNormComposite_mem_mulNat_range`: v_ℚ(N a) ∈ f_K ℤ̂, and the corestricted map `cyclotomicZHatNormCompositeInMulNatRange` has dense image in f_K ℤ̂.
- `normalizedCyclotomicZHatIdeleValue K`: v_K, with dense image in ℤ̂. `cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue`: f_K · v_K(a) = v_ℚ(N a). `normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion`: on rational ideles v_K = ([K : ℚ] / f_K) · v_ℚ.

## Proofs

The restriction formula is checked on each finite layer through norm functoriality of the global Artin maps (`globalArtinMonoidHom_norm_restriction`) and assembled in the inverse limit. The fixing statement writes N(a) as a norm from K ∩ T, by transitivity of the idele norm in a tower, and uses that norms lie in the kernel of the finite Artin map. Density follows from the finite-layer computation, which uses surjectivity of the finite Artin map, and the Krull neighbourhood basis.

## Watch for

- By its own account the file stops at the idele level. It does not show that v_K vanishes on principal ideles or descend it to C_K, and it proves no integer-value or norm-range identity for C_K.
- Dividing by f_K is division on the subgroup f_K ℤ̂ (`zHatDivide`), allowed only once membership is proved; [K : ℚ] / f_K is natural-number division, exact because f_K divides [K : ℚ].
- The Artin maps are the library's own, built from chosen local factors.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicIdeleValue.lean`: the Lean file is the source byte for byte (SHA-256 `9296eaa2930ad0788e678710bf1e3b3cb2a447136515aeb412160bde17012423`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
