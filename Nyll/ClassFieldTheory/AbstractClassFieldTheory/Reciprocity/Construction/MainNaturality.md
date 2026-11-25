# Naturality of the finite reciprocity map under norms and conjugation

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of the library, fields are closed subgroups of a profinite group `G`, and the finite reciprocity homomorphism `finiteReciprocityHom` sends `G(L/K)` (written additively) to the norm quotient `A(K) / N(L/K) A(L)` of a `G`-module `A`. This file proves its two naturality properties: compatibility with restriction of Galois groups against the norm `N(K'/K)`, and compatibility with conjugation by an element `s ∈ G`. The vertical maps are built directly on the finite Galois quotients and the finite norm quotients.

## Main definitions

- `finiteReciprocityNaturalityRestriction`: restriction `G(L'/K') → G(L/K)` for `K' ⊆ L'` over `K ⊆ L` with `L ⊆ L'`.
- `finiteReciprocityNaturalityNormMap`: the map `A(K')/N A(L') → A(K)/N A(L)` induced by `N(K'/K)`; it is well defined by transitivity of norms.
- `finiteReciprocityNaturalityConjugationNormMap`: the map `A(K)/N A(L) → A(K^s)/N A(L^s)` induced by `a ↦ a^s` (`conjugateFixedElementHom`).

## Main results

Both assume `G` profinite (compact, Hausdorff, totally disconnected) and the hypothesis `hAxiom : v.SatisfiesUnramifiedUnitCohomology D` for valuation data `v`.

- `finiteReciprocityNaturality_restriction_norm_commutes`: for a finite extension `K'/K` of fields of finite absolute degree and finite normal `L/K`, `L'/K'` with `L ⊆ L'`, the norm map composed with the reciprocity map of `L'/K'` equals the reciprocity map of `L/K` composed with restriction.
- `finiteReciprocityNaturality_conjugation_commutes`: for `K` of finite absolute degree, finite normal `L/K` and `s ∈ G`, the conjugation norm map composed with the reciprocity map of `L/K` equals the reciprocity map of `L^s/K^s` composed with conjugation of Galois groups.

## Proofs

For the first diagram, a Frobenius lift `σ` over `K'` is transported to `K` (`finiteReciprocityNaturalityFrobeniusTowerLift`), which multiplies its exponent by the residue degree `f(K'/K)`. The fixed field `Σ'` of `σ` contains the fixed field `Σ` of the transported lift, and `Σ'/Σ` is totally ramified (`finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified`, by comparing residue degrees), so the norm of a prime of `Σ'` is a prime of `Σ`. Each reciprocity value is then the class of the norm of a prime (`finiteReciprocityHom_apply_eq_primeNormClass`), and transitivity of norms closes the square. For the second diagram, conjugation preserves degree and inertia, gives a continuous isomorphism of Frobenius quotients, preserves exponents, and carries the fixed field of `σ` to that of its conjugate. Conjugates of primes are primes, and norms commute with conjugation (`relativeNorm_conjugate_apply`).

## Watch for

- Both commutativity theorems carry `hAxiom`, the library's axiom on the cohomology of unramified units, as a hypothesis.
- Fields are closed subgroups, so inclusions are reversed: `K' ≤ K` as subgroups means `K'` is an extension of `K`.
- The conjugate field `K^s` is the subgroup `s⁻¹Ks`, and `a ↦ a^s` is the action of `s⁻¹` on `A`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `f95f355ffce2a2ee3ed791efb0ea9039e223888aba1f4a17f2c4ea07b783b584`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
