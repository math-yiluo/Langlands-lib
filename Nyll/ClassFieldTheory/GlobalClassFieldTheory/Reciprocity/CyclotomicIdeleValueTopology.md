# Continuity of the cyclotomic idele values

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValueTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The rational cyclotomic value v_ℚ : I_ℚ → ℤ̂ is defined elsewhere as a continuous homomorphism in multiplicative form, and the normalized value v_K = (1/f_K) · v_ℚ ∘ N on the ideles of a number field K, with N the idele norm from K to ℚ, as a plain additive homomorphism. This file gives v_ℚ its continuous additive form, bundles v_K as a continuous homomorphism in additive and multiplicative form, studies the reductions of v_ℚ modulo n, and shows that v_K already has dense image on norm-one ideles.

## Main definitions and results

- `rationalCyclotomicZHatIdeleValueContinuousAdd`: v_ℚ as a continuous additive homomorphism `Additive (IdeleGroup ℚ) →ₜ+ ZHat`. It has dense image, and its kernel is closed.
- `rationalCyclotomicZHatIdeleValueReduction n hn`: v_ℚ reduced modulo a positive integer n, with values in `ZMod n`. It is surjective (dense image in a discrete space) and has open kernel.
- `cyclotomicZHatNormCompositeContinuous K`: v_ℚ ∘ N as a continuous homomorphism, using continuity of the idele norm (`IdeleGroup.norm_continuous`). `cyclotomicZHatNormCompositeInMulNatRangeContinuous K` is the same map with values in f_K ℤ̂, where f_K is `cyclotomicZHatIntersectionDegree K`.
- `normalizedCyclotomicZHatIdeleValueContinuous K` and its multiplicative form `normalizedCyclotomicZHatIdeleValueContinuousMul K`: v_K as a continuous homomorphism, equal pointwise to `normalizedCyclotomicZHatIdeleValue K`.
- `normalizedCyclotomicZHatIdeleValue_normOne_denseRange`: the norm-one ideles of K already have dense image under v_K.

## Proofs

The density on norm-one ideles reduces to density on all ideles: by `exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue`, from the imported norm-one correction file, every idele has a norm-one idele with the same value. The comments explain this by a positive archimedean correction whose cyclotomic value is trivial.

## Watch for

- Nothing here descends the values to idele class groups. The multiplicative v_K is only prepared for the descent through the principal ideles, which other files carry out.
- The number-field results take `K : Type`, in universe 0.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicIdeleValueTopology.lean`: the Lean file is the source byte for byte (SHA-256 `4579bee5917537d6def169e0beb8938e787fda50be2ff02f176509dd5f35682c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
