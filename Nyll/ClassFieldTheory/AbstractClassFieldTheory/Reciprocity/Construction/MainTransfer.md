# Transfer and the finite reciprocity map

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of the library, fields are closed subgroups of a profinite group `G` and `G(L/K)` is a quotient of closed subgroups. This file proves that the finite reciprocity map is compatible with the transfer (Verlagerung): for a finite normal extension `L/K` and an intermediate field `K'`, `r(L/K') ∘ Ver = ι ∘ r(L/K)`, where `Ver : G(L/K)^ab → G(L/K')^ab` and `ι : A(K)/N(L/K)A(L) → A(K')/N(L/K')A(L)` is induced by the inclusion `A(K) ⊆ A(K')`.

## Main definitions

- `transferNormNaturalityIntermediateInclusion`: the injective map `G(L/K') → G(L/K)`, with image `transferNormNaturalityIntermediateSubgroup` and the identification `transferNormNaturalityIntermediateQuotientEquiv`.
- `transferNormNaturalityTransfer`: Mathlib's `MonoidHom.transfer` to the abelianized image subgroup, transported to `G(L/K')^ab`.
- `transferNormNaturalityAbelianizedReciprocity`: the finite reciprocity homomorphism factored through `G(L/K)^ab`.
- `transferNormNaturalityNormWitness`: for `a ∈ A(L)`, the sum of the translates of `a` over a chosen right transversal of `G(L/K')` in `G(L/K)`.
- `transferNormNaturalityNormQuotientInclusion`: the map `ι`.

## Main results

- `transferNormNaturality_norm_doubleCoset_formula`: `N(L/K)(a) = N(L/K')(transferNormNaturalityNormWitness a)`; this makes `ι` well defined.
- `transferNormNaturality_transfer_doubleCoset_formula`: `Ver(σ)` is the product over the orbits of `⟨σ⟩` on `G(L/K)/G(L/K')` of `t⁻¹ σ^f t`, with `t` a representative of the orbit and `f` its length.
- `transferNormNaturalityTransfer_restriction_natural`: the transfer commutes with restriction from the Frobenius quotients (modulo inertia) to the finite Galois groups. Consequently (`transferNormNaturalityTransfer_frobenius_product`), the transfer of the restriction of a Frobenius element `σ` over `K` is the product of the restrictions of Frobenius lifts over `K'`, one for each orbit.
- `transferNormNaturality_generator_square`: the identity on the restriction of one Frobenius element.
- `transferNormNaturality`: `r(L/K') ∘ Ver = ι ∘ r(L/K)` as additive maps, for `G` profinite and fields of finite absolute degree.

## Proofs

Every element of `G(L/K)` is the restriction of a Frobenius element (`frobeniusRestriction_surjective`), so it suffices to check generators. For such a `σ` with prime element `π` of its fixed field `Σ`, each factor of `Ver(σ)` has as reciprocity value the class of the norm of a conjugate `π^t`, which is a prime of the factor's fixed field. The identity `N(Σ/K)(π) = Σ_q N(Σ_q/K')(π^(t_q))` (`transferNormNaturalityNorm_eq_sum_transferNorms`), reindexed by an equivalence of orbit sets, then matches the two sides.

## Watch for

- `transferNormNaturality` and `transferNormNaturality_generator_square` carry `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`, the library's axiom on unramified unit cohomology, as a hypothesis.
- In `transferNormNaturality`, `transferNormNaturality_generator_square` and the two double-coset formulas, normality of `L/K'` and, where it is needed, finiteness of `G(L/K')` are derived inside the statements, not assumed; `transferNormNaturalityTransfer_restriction_natural`, `transferNormNaturalityTransfer_frobenius_product` and the definitions that involve `K'` take normality of `L/K'` as an instance hypothesis.
- The witness depends on a chosen transversal (`Quotient.out`); only its norm enters the results.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`: the Lean file is the source byte for byte (SHA-256 `33c239403974922e938bdd7185bac7a25d4f778abdaba7095b78f14b375c5992`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
