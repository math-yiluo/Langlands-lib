# The finite reciprocity homomorphism G(L | K) → A_K / N(L|K) A_L

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The final step of the abstract construction of the reciprocity map, for a profinite group `G`, a `G`-module `A`, a degree map `D` and valuation data `v`. For `K` a `FiniteAbstractField` (finite over the base field) and a finite Galois extension `L | K`, the reciprocity map of earlier files sends each Frobenius element `σ` of `G(L̃ | K)` to the class of `N(Σ|K)(π_Σ)`, with `π_Σ` a prime element of the fixed field `Σ` of `σ`. Here it is pushed to `A_K / N(L|K) A_L` and descends along restriction to an additive homomorphism on `G(L | K)`, an isomorphism when `L | K` is unramified.

## Main definitions and results

- `finiteReciprocityValue`: the value of `σ` in `A_K / N(L|K) A_L`. With `hAxiom`, it is additive on the Frobenius semigroup (`finiteReciprocityValue_mul`) and any prime element of `Σ` may be used (`finiteReciprocityValue_eq_primeNormClass_of_isPrime`).
- `frobeniusLiftDifference`: for exponents `d(σ) < d(τ)`, the Frobenius element `σ⁻¹τ` of exponent `d(τ) − d(σ)`, trivial on `L` when `σ` and `τ` have the same restriction.
- `finiteReciprocityValue_eq_zero_of_restriction_eq_one`: a Frobenius element trivial on `L` has value zero, since then `Σ ⊇ L`.
- `finiteReciprocityHom_lift_comparison`: two Frobenius elements with the same restriction are equal, or one is the other times a Frobenius element of value zero.
- `chosenFiniteReciprocityFrobeniusLift`, `finiteReciprocityCandidate`: a chosen lift of each `q ∈ G(L | K)` and its value; `finiteReciprocityHom_of_mul` is the homomorphism with additivity on Frobenius elements as a hypothesis.
- `finiteReciprocityHom D A v hAxiom K L hLK : Additive G(L | K) →+ A_K / N(L|K) A_L`; by `finiteReciprocityHom_apply_eq_primeNormClass` its value at `q` is the class of `N(Σ|K)(π)` for any Frobenius lift of `q` and any prime element `π` of its fixed field.
- Unramified `L | K`: the fixed field of the degree-one lift has degree `1` over `K` and the prime element of `K` stays prime there (`unramifiedFrobenius_fixedField_degree`, `unramifiedFrobenius_includedPrime_isPrime`); `unramifiedReciprocity_frobenius_image`: Frobenius goes to the class of the prime element of `K`; `unramifiedReciprocity_bijective_of_generator`: any homomorphism with this value is bijective; `unramifiedReciprocityEquiv`: the resulting isomorphism.

## Proofs

In the unramified case the prime class generates `A_K / N(L|K) A_L`, cyclic of order `[L : K]` by earlier files, so a homomorphism hitting it is surjective between groups of equal order.

## Watch for

- `hAxiom : v.SatisfiesUnramifiedUnitCohomology D` (vanishing of `Ĥ⁰` and `Ĥ⁻¹` of units in unramified cyclic extensions) is a hypothesis of the homomorphism and of the unramified isomorphism.
- The docstring speaks of the finite reciprocity equivalence, but for general `L | K` the file constructs a homomorphism only; bijectivity is proved only in the unramified case.
- `G(L | K)` enters as `Additive (G_K / G_L)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainFiniteReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `c4eafef84efd827491c8dbb5233e8d2d5b41dc20e083cbb696d42986a5e8edae`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
