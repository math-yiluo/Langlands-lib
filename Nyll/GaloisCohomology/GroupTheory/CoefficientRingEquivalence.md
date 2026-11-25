# Changing the coefficient ring of representations along a ring isomorphism

Module `Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A ring isomorphism `e : R ≃+* S` turns every S-linear representation of a monoid G into an R-linear one with the same underlying group, the same action and the same equivariant maps, r acting as `e r`. The file sets up this equivalence of categories and shows that it does not change group cohomology. Its main use is `ULift.ringEquiv : ULift ℤ ≃+* ℤ`, which brings integral representations into a coefficient ring of a higher universe.

## Main definitions and results

- `Rep.coefficientRingEquivalence e G : Rep S G ≌ Rep R G`, built from Mathlib's `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`. `rfl` lemmas say that the carrier, the action and the underlying functions of morphisms are unchanged and scalars act through e. It commutes with restriction along `q : H →* G` and is additive.
- `Rep.coefficientRingEquivalence_obj_norm_apply`: for G a finite group, the norm is unchanged.
- `Rep.coefficientRingInvariantsNatIso`: for commutative rings, taking invariants commutes with the transport, naturally.
- `ModuleCat.coefficientRingAddHom`: for `e : R ≃+* ℤ`, an additive map of ℤ-modules is a morphism after restriction of scalars.
- `groupCohomology.coefficientRing_d₁₂_apply`: the degree-one coboundary of the transported representation is given by the usual formula in the original action.
- `groupCohomology.coefficientRingCochainsIso` and `coefficientRingComplexIso`: the inhomogeneous cochain complex of A with scalars restricted along e is isomorphic to that of the transported representation, by the identity on cochains.
- `groupCohomology.coefficientRingIso n`: `Hⁿ(G, A)` with scalars restricted along e is isomorphic to `Hⁿ(G, A')`, A' the transported representation.

## Proof

The cochain groups are the same functions; the differentials agree because e sends the signs `(−1)^(j+1)` of R to those of S. Cohomology is then the homology of isomorphic complexes, after commuting homology with restriction of scalars.

## Watch for

- The equivalence allows R, S, G and the carriers in independent universes, but the cohomology comparison requires R and S commutative, G a group, and R, S, G and the carrier all in one universe u, as Mathlib's group cohomology does.
- The equivalence goes from S-representations to R-representations: it restricts scalars along e.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/CoefficientRingEquivalence.lean`: the Lean file is the source byte for byte (SHA-256 `a5be516c05c4828a9c9d88575962b6ccb5c66fdcb49feb3c3d90704f82bdcef4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
