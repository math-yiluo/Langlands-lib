# Galois action on S-units and their logarithmic lattice

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be an extension of number fields, G = `L ≃ₐ[K] L`, and S a finite set of finite places of L. This file makes G act on the places of L, on Lˣ, on the S-unit group and on the logarithmic coordinate space, and proves that the logarithm is equivariant. It then enlarges the logarithmic lattice by one invariant diagonal direction. When G is cyclic, the Herbrand quotient of the enlarged lattice is computed as a product of stabilizer orders.

## Actions

- `finitePlaceEquiv K L σ`: the permutation of the finite places of L induced by σ on 𝓞 L. `finitePlaceMulAction` makes it an action. `valuation_finitePlaceEquiv` and `adicAbv_finitePlaceEquiv` say that the valuation and the normalized absolute value at σv of σx equal those at v of x.
- `fieldUnitsMulDistribMulAction`: the action of G on Lˣ.
- `IsGaloisStableFinitePlaces K L S`: v ∈ S if and only if σv ∈ S, for all σ and v. Under this hypothesis, `sUnitMulDistribMulAction` restricts the action to `SUnitGroup S`. `logPlaceMulAction` acts on `LogPlace S`, the infinite places together with S. `fullLogSpaceDistribMulAction` acts on the coordinate space by (σz)(p) = z(σ⁻¹p), and `permutationRepresentation_logPlace` identifies it with `permutationRepresentation` of `logPlacePermutationHom`.

## The logarithm

- `fullLogAmbient_smul` and `fullLog_smul`: the logarithmic map on S-units commutes with G. This uses `infinitePlace_mult_smul`, which says that multiplicities at infinite places are constant on orbits.
- `fullLog_ker_eq_torsion` and `additiveSUnitQuotientTorsionEquivFullLogLattice`: the kernel is the torsion, so S-units modulo torsion are isomorphic to `fullLogLattice S`. `fullLogLattice_smul_mem` says the lattice is G-stable.
- `fullLogSpaceEquivHyperplaneProd`: the coordinate space splits as the sum-zero hyperplane times ℝ, via the constant vector `normalizedLogDiagonal` with coordinate sum 1.
- `extendedFullLogLattice L S`: the preimage of `fullLogLattice S` × ℤ under this splitting. Instances show that it is a full ℤ-lattice. `extendedFullLogLattice_permutation_stable` says that it is stable under the permutation representation.

## Herbrand quotient

- `extendedFullLogPermutationSublattice_finite_quotient`: the canonical permutation sublattice of the extended lattice has finite index.
- `extendedFullLogLattice_herbrandQuotient_eq_stabilizerProduct`: if every element of G is a power of σ, the Herbrand quotient of the extended lattice for σ is defined. It equals the product, over the G-orbits of logarithmic places, of the orders of their stabilizers. The proof applies the imported `completePermutationLattice_herbrandQuotient_eq_stabilizerProduct`.

## Points to watch

- The Herbrand quotient is computed for the extended lattice, which is log(S-units) plus one diagonal ℤ-direction. It is not computed for the S-unit group itself.
- S contains only finite places. All infinite places are always added as coordinates.
- Cyclicity enters as the hypothesis `hgen`. No Galois hypothesis is made: G is the group of all K-automorphisms of L.
- The actions are reducible definitions, used only as local instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean`: the Lean file is the source byte for byte (SHA-256 `fc59c88a87b0ee23ea2af27e09b3ed2a597b76c56e7917d6eace6795161bdcb4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
