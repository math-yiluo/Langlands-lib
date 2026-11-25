# The degree map on any algebraic closure of a finite field

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `k` be a finite field and `Ω` any algebraically closed algebraic extension of `k`. The residue field produced by a valuation ring of a separable closure is such a field but is not Mathlib's `AlgebraicClosure k`, so the identification of `Gal(Ω/k)` with `ZHat` by arithmetic Frobenius is redone here for arbitrary `Ω`. Its inverse is the degree map used in finite local reciprocity.

## Main definitions and results

- Instances: `Ω` is an algebraic closure of `k`, Galois over `k`, with Hausdorff Galois group.
- `residueAbsoluteFrobenius_isAlgClosure_injective` and `residueAbsoluteFrobenius_isAlgClosure_surjective`: the Frobenius map `ZHat → Gal(Ω/k)` is bijective; injectivity is detected on finite subextensions of every degree, surjectivity because the closed image has fixed field `k`.
- `residueAbsoluteFrobeniusEquivIn`: the resulting isomorphism of topological groups `ZHatMul ≃ₜ* Gal(Ω/k)` (`ZHatMul` is `ZHat` written multiplicatively).
- `residueAbsoluteDegreeIn k Ω`: its inverse, a continuous homomorphism `Gal(Ω/k) → ZHatMul`, with `residueAbsoluteDegreeIn_frobenius` sending arithmetic Frobenius to `Multiplicative.ofAdd (1 : ZHat)`, the element `1` of `ZHat`.
- `eq_frobeniusAlgEquivOfAlgebraic_of_residueAbsoluteDegreeIn` and `apply_eq_pow_card_of_residueAbsoluteDegreeIn`: an automorphism of degree `Multiplicative.ofAdd (1 : ZHat)` is arithmetic Frobenius, `x ↦ x^q` with `q = #k`, not its inverse.
- `residueAbsoluteDegreeIn_semilinear_conjugation`: the degree is unchanged under conjugation by a ring isomorphism `Ω ≃ Ω'` lying over an isomorphism of finite fields `k ≃ k'`.
- `residueAbsoluteFrobenius_restrictScalars` and `residueAbsoluteDegreeIn_restrictScalars`: for a finite intermediate field `E`, an automorphism over `E`, viewed over `k`, has degree `[E : k]` times its degree over `E`.
- `finiteResidueFrobeniusExponentEquiv_symm_restrict_in`: on a finite Galois subextension `E`, the restriction of `σ` corresponds to its degree reduced modulo `[E : k]`.

## Proofs

The conjugation and base-change formulas compare two continuous homomorphisms out of `ZHat` that agree on `1`; they then agree on the dense image of `ℤ`, hence everywhere.

## Points to watch

The definition uses only the Frobenius homomorphism of `Ω` itself: no isomorphism with a chosen algebraic closure and no choice of generator of a finite cyclic group enters it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`: the Lean file is the source byte for byte (SHA-256 `5c039ea26e6f3f4865b0210101b1e296d40de0b7775d81d2109390528a6a17a7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
