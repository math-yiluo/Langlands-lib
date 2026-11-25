# Unit descent on Frobenius fixed-field towers

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FixedTowerUnitDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Part of the abstract proof of the universal norm-descent lemma, for a profinite group `G`, a `G`-module `A` written additively, a degree map `D` and valuation data `v`. A Frobenius fixed-field tower consists of the fixed fields `S ⊆ T` of two commuting Frobenius elements `σ`, `σn` of an extension `L | K`. Given an equation `φ u − u = Σᵢ (τᵢ uᵢ − uᵢ)` between units of `S`, the file lifts it to units of `T`, corrects it by a term `σ ȳ − ȳ`, and obtains an equation of the same shape in the invariants of the maximal unramified extension `L̃` of `L`.

## Main definitions and results

- `ValuationData.fixedTowerUnitAction`: the action on the units of `T` of a class commuting with the upper Frobenius.
- `ValuationData.powerTowerCorrection`: for a power-fixed-field tower `P` (where `σ = φⁿ` and `σn = φ^(n²)` for a Frobenius `φ` of exponent one), the upper unit `(φ ū − ū) − Σᵢ (τᵢ ūᵢ − ūᵢ)`, with the `τ i` in the kernel of the normalized degree map.
- `unitRepresentation_generator_action_eq`: the lower Frobenius acts on the units of `T` as the class in `Gal(T | S)` of any `Representative` of it in the unit representation.
- `universalNormDescent_fixedTower_solution`: for a power-fixed-field tower `P`, assume `hAxiom : v.SatisfiesUnramifiedUnitCohomology`. If `φ u − u = Σᵢ (τᵢ uᵢ − uᵢ)` for units `u`, `uᵢ` of `S` (hypothesis `hstar`), with each `τ i` commuting with both Frobenius elements, there are units `ū`, `ūᵢ`, `ȳ` of `T` with `N(ū) = u`, `N(ūᵢ) = uᵢ` and `σ ȳ − ȳ` equal to the correction term.
- `maximalNorm_relativeNorm_fixedTower`: for a tower of degree `n` with `L | K` finite, a cyclic generator and a unit `a` of `T`, the norm `N(L̃|K̃)` of the image of `N(T|S)(a)` equals `Σ σⁱ` (`i < n`) applied to `N(L̃|K̃)` of the image of `a`.
- `universalNormDescent_correctedEquation`: if `σ ȳ − ȳ` equals the correction term and `σ = φ^n`, then `w = ū − (1 + φ + … + φⁿ⁻¹) ȳ`, computed in the invariants of `L̃`, satisfies `φ w − w = Σᵢ (τᵢ ūᵢ − ūᵢ)`.

## Proofs

The tower is an unramified cyclic extension with an explicit generator; vanishing of Tate `Ĥ⁰` of the units gives the norm lifts `ū`, `ūᵢ`; the correction term has norm zero by the preceding file; vanishing of `Ĥ⁻¹` gives `ȳ`. The corrected equation is a telescoping computation.

## Watch for

- `hAxiom : v.SatisfiesUnramifiedUnitCohomology` is a hypothesis: vanishing of `Ĥ⁰` and `Ĥ⁻¹` of units in unramified cyclic extensions is assumed.
- The equations `hstar` and `hyBar` are hypotheses; actions go through `Quotient.out` representatives.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean`: the Lean file is the source byte for byte (SHA-256 `f0b04e17fb1ed293ce6446b7d74d67ca3e68b1432c43be1acb7a71703467e6a1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
