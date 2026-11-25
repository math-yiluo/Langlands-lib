# Tate cohomology in degrees 0 and −1 as concrete quotients

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file compares `tateCohomology` of the `ℤ`-representation `Rep.ofMulDistribMulAction G A` attached to a multiplicative `G`-module `A`, which its comments call Mathlib's Tate cohomology, with the library's quotients `HerbrandH0 G A = A^G / N_G A` and `HerbrandHMinusOne G A σ = ker N_G / I_G A`. It also turns equivariant homomorphisms and short exact sequences of multiplicative modules into morphisms and short exact sequences of representations.

## Main definitions and results

- `equivariantRepHom f hf`: an equivariant `f : A →* B` as a morphism of representations (`equivariantRepHom_apply`).
- `equivariantShortComplex i j hi hj hker` and `equivariantShortComplex_shortExact`: if `ker j = im i`, `i` is injective and `j` surjective, the resulting short complex of representations is short exact.
- `repNorm_toMul`: the norm of the representation is `tateNorm`. `repSigmaMinusOne_toMul`: for commutative `G`, `ρ(σ) − 1` is `sigmaMinusOne`.
- `fixedCyclesAddEquiv`: the kernel of `groupCohomology.d₀₁` is additively isomorphic to `fixedSubgroup G A`; `normKernelCyclesAddEquiv`: the kernel of the representation norm is additively isomorphic to `normKernelSubgroup G A`.
- `tateH0IsoHerbrandH0 : tateCohomology (Rep.ofMulDistribMulAction G A) 0 ≅ ModuleCat.of ℤ (Additive (HerbrandH0 G A))`, for any finite `G`.
- `tateHMinusOneIsoHerbrandHMinusOne σ hgen`: the same in degree −1 with `HerbrandHMinusOne G A σ`, for `σ` generating `G`. `tateHMinusOneIsoHerbrandHMinusOne_of_commGroup` is the version for commutative `G`; the general one reduces to it by giving `G` the commutative structure that comes from cyclicity.

## Proofs

Degree 0 goes through `TateCohomology.isoZeroBoundary` and the short complex "norm, then `d₀₁`"; degree −1 through `TateCohomology.isoFiniteCyclicNegOne` and `Rep.FiniteCyclicGroup.subCompNormHom`. In both, cycles are matched with the fixed subgroup or the norm kernel, boundaries with the norm image or the augmentation image, and the homology with the quotient.

## Points to watch

- `fixedCyclesAddEquiv`, `tateH0IsoHerbrandH0` and the two degree −1 isomorphisms take `G A : Type`, so they hold only in universe 0. `repNorm_toMul`, `normKernelCyclesAddEquiv` and the constructions on representations are universe-polymorphic; the latter take `A`, `B`, `C` in one common universe, independent of that of `G`.
- `repSigmaMinusOne_toMul` assumes `G` commutative.
- The degree-0 isomorphism needs no generator; the degree −1 isomorphisms depend on the chosen `σ`.
- `HerbrandH0` and `HerbrandHMinusOne` are the library's own models; they enter through `Additive` as objects of `ModuleCat ℤ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`: the Lean file is the source byte for byte (SHA-256 `5143cd1737e89bc63ef86598fe624b039240b152c11b2b6af750cf5ab404822f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
