# Galois action on relative ideles and their local components

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. The group of K-automorphisms σ of L acts on 𝔸_K ⊗_K L through the factor L. This file shows that this action commutes with taking the component at each place. As a consequence, the library's identification of relative ideles with a restricted product of local tensor units is equivariant, and the action on the restricted product is conjugation place by place.

## Definitions

- `relativeIdeleRestrictedMulDistribMulAction`: the action on `RelativeIdeleGroup K L`, upgraded to an action by group automorphisms.
- `scalarTensorConjugation σ`: for any commutative K-algebra A, the A-algebra automorphism id ⊗ σ of A ⊗_K L. `scalarTensorConjugation_tmul`, `_one` and `_mul` give its value on pure tensors and the action laws.
- `scalarTensorUnitsAction`: the resulting action on the units (A ⊗_K L)ˣ.
- `relativeLocalIdeleDataMulDistribMulAction`: the action on the restricted product `RelativeLocalIdeleData`, transported along the equivalence `relativeIdeleMulEquivLocalData` from relative ideles.

## Results

- `relativeAdeleInfiniteComponent_conjugation` and `relativeAdeleFiniteComponent_conjugation`: the component of the conjugate σ(z) of a relative adele at an infinite or finite place w is the conjugate of the component of z.
- `RelativeIdeleGroup.infiniteComponent_smul` and `RelativeIdeleGroup.finiteComponent_smul`: the same for the unit components of relative ideles.
- `relativeIdeleMulEquivLocalData_smul`: the equivalence between relative ideles and `RelativeLocalIdeleData` is equivariant.
- `RelativeLocalIdeleData.infinite_smul` and `RelativeLocalIdeleData.finite_smul`: the transported action acts on each infinite and finite coordinate by `scalarTensorUnitsAction`.

## Proofs

The component statements are checked on pure tensors and extended by additivity. The equivariance of the equivalence holds by construction of the transported action. The coordinate formulas combine it with the component statements.

## Points to watch

- The action on `RelativeLocalIdeleData` is defined by transport along the equivalence. Its coordinatewise description is a theorem.
- The actions are definitions, not global instances, so a statement that uses one activates it locally.
- L/K is not assumed Galois. The acting group is the group of K-automorphisms of L.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/RestrictedAction.lean`: the Lean file is the source byte for byte (SHA-256 `54a1927ff30fe9a52412edb88e1c3c622c3720b0fece0a06c48943d91264e5dd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
