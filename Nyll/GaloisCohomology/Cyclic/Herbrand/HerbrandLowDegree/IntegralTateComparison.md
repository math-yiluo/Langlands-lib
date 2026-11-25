# Integral Tate groups in degrees 0 and −1 as concrete quotients

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.IntegralTateComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G`, a multiplicative `G`-module `A` and a generator `σ` of `G`, the file identifies the homology of the two short complexes built from the norm and from `σ − 1` on the representation `Rep.ofMulDistribMulAction G A` with the library's quotients `HerbrandH0 G A = A^G / N_G A` and `HerbrandHMinusOne G A σ = ker N_G / I_G A`. Composing with comparisons from the imported files, it identifies the integral Tate groups `tate (Rep.ofMulDistribMulAction G A) 0` and `tate (Rep.ofMulDistribMulAction G A) (-1)` with these quotients.

## Main definitions

- `cyclicFixedCyclesAddEquiv σ hgen`: the kernel of `ρ(σ) − id` is additively isomorphic to `fixedSubgroup G A`.
- `normHomologyEquivHerbrandH0 σ hgen`: the homology of `normHomCompSub` (norm, then `σ − 1`) is `≃+ Additive (HerbrandH0 G A)`.
- `subNormHomologyEquivHerbrandHMinusOne σ`: the homology of `subCompNormHom` (`σ − 1`, then norm) is `≃+ Additive (HerbrandHMinusOne G A σ)`.
- `integralTateH0EquivHerbrandH0 σ hgen : tate (Rep.ofMulDistribMulAction G A) 0 ≃+ Additive (HerbrandH0 G A)`.
- `integralTateHMinusOneEquivHerbrandHMinusOne σ hgen : tate (Rep.ofMulDistribMulAction G A) (-1) ≃+ Additive (HerbrandHMinusOne G A σ)`.

## Proofs

Cycles are matched with the fixed subgroup (using the generator) or with the norm kernel, and boundaries with the norm image or the augmentation image, using `repNorm_toMul`; the homology is then the quotient by the kernel of the class map. The Tate statements compose these with `normHomologyEquivTateZero` and `subNormHomologyEquivTateMinusOne`.

## Points to watch

- The results are isomorphisms of additive groups (`≃+`) with `Additive` of the multiplicative quotients, not isomorphisms in `ModuleCat`.
- `tate` is the Tate cohomology opened from the namespace `IntegralGroupCohomology.Universe`, which the file calls the existing integral Tate owner; it is a different declaration from the `tateCohomology` compared with the same quotients in the imported `TateComparison` module.
- `G` and `A` have independent universes.
- Both Tate equivalences take the hypothesis that `σ` generates `G`; the degree −1 quotient also depends on `σ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/IntegralTateComparison.lean`: the Lean file is the source byte for byte (SHA-256 `5c61da5eb09eed572480535a4b91b4c0051a0c634c279bd22a455915dfe5169d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
