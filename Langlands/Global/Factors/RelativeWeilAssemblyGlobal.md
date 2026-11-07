# The global product package of a Brauer decomposition

## Contents

This module supports the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
It builds, from the Hecke global functional equation, the functional-equation package on the
finite places of a number field `F` that matches a Brauer decomposition
`d · [χ] + Σ_i r_i · Ind_{K_i}([λ_i] − [λ'_i])`. The Hecke statement
(`HeckeGlobalFunctionalEquationStatement`) is an explicit hypothesis `hH` and is not proved
here. All names are in namespace
`Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine`. `ψ` is a nontrivial
character of `A_F` trivial on `F`.

### Additive components over an extension

- `traceComponents ψf u`: for finite additive components `ψf` of `ψ` at the places of `F` and
  a finite place `u` of an extension `K`, the character `localTraceCharacter` at `u` of
  `ψf (u.under (𝓞 F))`, i.e. `ψf_p ∘ Tr_{K_u/F_p}` with `p` the place below `u`.
- `isFiniteAdditiveComponent_traceComponents`: if each `ψf v` is the component of `ψ` at `v`,
  then `traceComponents ψf u` is the component at `u` of the published `traceAdditiveCharacter ψ hψ`.
- `exists_traceAdditiveCharacter_ne_one`: that character is nontrivial, as the Hecke
  statement requires.

### Packages

- `hasGlobalEquation_heckePushforward` (hypothesis `hH`): for a Hecke character `λ` of a
  finite extension `K` of `F`, self-dual measures `μK` for `traceComponents ψf`, archimedean
  data `D : HeckeArchData λ (traceAdditiveCharacter ψ hψ)`, and a finite set `B` of places of
  `F` such that the finite epsilon factors of `λ` at the places above every `z ∉ B` are `1`,
  there is a package on the finite places of `F`. Its local factors at `z` are the products over
  `placesAbove K z` of `heckeL λ`, `heckeL λ⁻¹` and `finiteEpsilon λ (traceComponents ψf) μK`.
  Its archimedean functions are `D.A`, `D.Ad`, `D.Ae`, and its exceptional set is `B`.
- `hasGlobalEquation_heckeBase` (hypothesis `hH`): the same for a Hecke character `χ` of `F`
  with components `ψf`, measures `μ` and data `D : HeckeArchData χ ψ`, without regrouping.
- `hasGlobalEquation_brauerProduct` (hypothesis `hH`): for an integer `d`, a Hecke character
  `χ` of `F`, integers `r i`, intermediate fields `K i` of a finite extension `E / F`, Hecke
  characters `λ i`, `λ' i` of `K i`, archimedean data `DF`, `DK i`, `DK' i`, measures `μ`,
  `μK i`, and a set `B` off which all the relevant finite epsilon factors are `1`, the product
  `(package of χ)^d · Π_i (regrouped package of λ i / regrouped package of λ' i)^{r i}` is a
  package with exceptional set `B`. Its local factors, dual factors, epsilon factors and
  archimedean functions are written out explicitly in the statement.

### Archimedean factors at one place

- `lumpedArch w₀ A Ad Ae`, the main definition: the family of `LocalFactors` over a finite type
  `I` with factors `A`, `Ad`, `Ae` at `w₀` and `1` elsewhere. The target statement only asks for
  some archimedean block, chosen before the twist. `lumpedArch_prod_lFactor`,
  `lumpedArch_prod_dualLFactor` and `lumpedArch_prod_epsilonFactor` compute the products over
  `I`. `lumpedArch_nonzeroMeromorphic` gives nonzero meromorphy of every factor when `A`,
  `Ad`, `Ae` are nonzero meromorphic.

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`): Theorem (3.5.3) and the paragraph after it,
printed p.16 (PDF p.25), obtains the functional equation for representations of Weil groups by
multiplying Hecke functional equations through (2.3.1) and (2.3.5). Theorem (3.4.1), printed
pp.14–15, uses `ψ ∘ Tr` for an extension. This module is internal bookkeeping that carries out
this multiplication and regrouping with the published engine and the published Hecke
statement. The placement of the whole archimedean block at one place is a convenience allowed
by the existential archimedean block of the target statement.

## Proof

- `isFiniteAdditiveComponent_traceComponents` applies
  `isFiniteAdditiveComponent_traceAdditiveCharacter` at the place `u.under (𝓞 F)`, with `u` as a
  place above it (`liesOver_under`). `exists_traceAdditiveCharacter_ne_one` is the
  nontriviality field of the published character.
- `hasGlobalEquation_heckePushforward`: `hasGlobalEquation_of_heckeArchData` for `λ` and
  `traceAdditiveCharacter ψ hψ` gives a package with some exceptional set `S` of places of `K`,
  off which the epsilon factors are `1`. `HasGlobalEquation.pushforwardPlaces` regroups it with
  exceptional set `B ∪ (S under F)`. `HasGlobalEquation.changeSet` then shrinks the set to `B`,
  since the regrouped epsilon factors off `B` are products of `1`.
- `hasGlobalEquation_heckeBase` is `hasGlobalEquation_of_heckeArchData` followed by
  `HasGlobalEquation.changeSet`.
- `hasGlobalEquation_brauerProduct` combines these with `HasGlobalEquation.zpow`, `.inv`,
  `.mul` and `hasGlobalEquation_finsetProd` of the published engine.
- The `lumpedArch` lemmas use `Finset.prod_eq_single` at `w₀`.
