# Herbrand quotients of field units as Tate cohomology

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L/K` with finite automorphism group `G = Gal(L/K)`, the library defines the multiplicative Herbrand groups `H⁰ = (Lˣ)^G / N(Lˣ)` and `H⁻¹ = (norm-one units) / ⟨g·x / x⟩` directly on `Lˣ`, while Mathlib defines Tate cohomology for the representation of `G` on `Additive Lˣ` (`Rep.ofAlgebraAutOnUnits K L`). This file identifies the two in degree `0` and, when `L/K` is finite and `g` generates `G`, in degree `−1`, so that statements proved for one transfer to the other.

## Main definitions and results

- `unitsNormLinearMap_toMul_eq_tateNorm`: the norm of the unit representation, read multiplicatively, is the library's `tateNorm`, the product of all Galois conjugates.
- `herbrandH0MulEquivInvariantsNormQuotient`: `HerbrandH0 G Lˣ` is isomorphic to the invariant submodule of `Additive Lˣ` modulo norms (in multiplicative form).
- `herbrandH0EquivTateCohomologyZero`: a bijection `HerbrandH0 G Lˣ ≃ tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0`, for `[Fintype Gal(L/K)]`; `cardinalMk_herbrandH0_fieldUnits_eq_tateCohomology_zero` records equal cardinalities.
- `herbrandHminusOneMulEquivUnitsBoundaryQuotient`: for `g ∈ G`, `HerbrandHMinusOne G Lˣ g` is isomorphic to `ker N / im(ρ(g) − 1)`.
- `unitsTateHminusOneIsoBoundaryQuotient`: if `L/K` is finite and `g` generates `G`, Mathlib's `tateCohomology … (−1)` is isomorphic to the same quotient.
- `herbrandHminusOneEquivUnitsTateHminusOne` and `cardinalMk_herbrandHminusOne_fieldUnits_eq_unitsTateHminusOne`: the resulting bijection and equality of cardinalities, without any finiteness hypothesis on the groups.
- Helpers: polymorphic constructions for maps into multiplicative forms of additive quotients (`additiveEquivToQuotientHom`, `quotientMulEquivOfSurjectiveAdditiveQuotient`, …), the identification `additiveNormKernelEquivUnitsNormKer` of norm-one units with the kernel of the norm, and `unitsRhoSubToNormKerLinearMap`, the map `ρ(g) − 1` into that kernel.

## Proofs

Each identification is a first isomorphism theorem: a surjection onto the additive quotient whose kernel is the multiplicative norm subgroup (degree `0`) or the augmentation subgroup (degree `−1`). In degree `−1` the comparison with Mathlib uses the finite-cyclic presentation of Tate cohomology (`TateCohomology.isoFiniteCyclicNegOne` and the homology of `subCompNormHom`).

## Remarks

- Both comparisons with Mathlib's Tate cohomology are bijections of types (`≃`), not group isomorphisms. The degree-zero one needs only `[Fintype Gal(L/K)]`; the degree `−1` one needs `L/K` finite and `Gal(L/K)` cyclic with generator `g`.
- In the second part `K` and `L` live in `Type`.
- `HerbrandH0` and `HerbrandHMinusOne` are the library's own groups.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`: the Lean file is the source byte for byte (SHA-256 `04874635d7d9cb77dc540dd8b4118675b031815a0c0f1a5da8ae4ce3f3579ea2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
