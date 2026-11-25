# Principal ideles as a Galois module

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields with Galois group G = Gal(L/K). This file identifies Lˣ with the subgroup of principal ideles inside the relative idele group of L over K, compatibly with the action of G. It then transfers the degree 0 cohomology group, the library's σ-dependent degree −1 group and the Herbrand quotient along this identification.

## Main definitions and results

- `fieldUnitsEquivPrincipalIdeles K L`: the isomorphism from Lˣ to `RelativeIdeleGroup.principalSubgroup K L`, induced by the diagonal embedding, which is injective.
- `fieldUnitsEquivPrincipalIdeles_smul`: this isomorphism commutes with the action of every σ ∈ G.
- `fieldUnitsHerbrandH0EquivPrincipalIdeles`: the isomorphism of the library's `HerbrandH0` groups of Lˣ and of the principal ideles.
- `fieldUnitsHerbrandHMinusOneEquivPrincipalIdeles σ`: the same for the library's `HerbrandHMinusOne` groups, which are formed with an element σ of G.
- `principalIdelesHerbrandQuotientDefined`: if the Herbrand quotient of Lˣ for σ is defined, so is that of the principal ideles.
- `fieldUnits_herbrandQuotient_eq_principalIdeles`: in that case the two Herbrand quotients are equal.

## Proof

Each of the four cohomological statements applies a general transfer result along the equivariant isomorphism: `herbrandH0EquivariantMulEquiv`, `herbrandHMinusOneEquivariantMulEquiv`, the matching finiteness lemmas, and `herbrandQuotient_eq_of_equivariantMulEquiv`.

## Points to watch

- `HerbrandQuotientDefined` is the condition that both cohomology groups are finite. Here it is a hypothesis on Lˣ, and the file does not prove it.
- σ is an arbitrary element of G, and the file does not assume that G is cyclic or that σ generates it. `HerbrandHMinusOne` is the norm kernel modulo the image of a ↦ σ(a)/a. It is the usual degree −1 Tate cohomology group when σ generates G, and need not be otherwise.
- The equivariance lemma and the two Herbrand-quotient results are stated without the Galois hypothesis. In them G is the group of K-automorphisms of L.
- `RelativeIdeleGroup`, its principal subgroup and the Galois actions on them are the library's own constructions, from imported files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Principal.lean`: the Lean file is the source byte for byte (SHA-256 `0dc5b13906064f6ef8820fdaf596470420c303c24cd114a45712a2ba2cd232a5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
