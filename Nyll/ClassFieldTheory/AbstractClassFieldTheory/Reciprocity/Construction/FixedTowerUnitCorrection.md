# The unit correction term on a Frobenius fixed-field tower

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FixedTowerUnitCorrection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A step in the abstract construction of the reciprocity map, in the setting of a profinite group `G` (compact, Hausdorff, totally disconnected), a `G`-module `A` written additively, a degree map `D` and valuation data `v`. Fix a finite residue abstract field `K`, a closed subgroup `L ≤ K` with `L` normal in `K`, and two Frobenius elements `σ`, `σn` whose fixed fields satisfy `Σn ⊇ Σ` (that is, the subgroup of `Σn` lies in that of `Σ`), with finite index conditions. The file builds the unit on the upper fixed field `Σn` whose vanishing norm makes it possible to apply the triviality of `H⁻¹` in the next step.

## Main definitions and results

- `ValuationData.fixedTowerCorrection`: given classes `φ` and `τ i` (a family indexed by a type `ι`) of `K` modulo inertia, each commuting with `σn`, a unit `ū` and units `ūᵢ` of the fixed field of `σn`, and a finite subset `s` of `ι` over which the sum runs, the unit `(φ ū − ū) − Σᵢ (τᵢ ūᵢ − ūᵢ)`, where the action is the unit action `frobeniusFixedFieldUnitAction` of the previous file.
- `fixedTowerCorrection_coe`: the same formula for the underlying elements of the invariants of `Σn`.
- `fixedTowerCorrection_relativeNorm_eq_zero`: suppose in addition that `φ` and each `τ i` commute with `σ`, that `u`, `uᵢ` are units of the fixed field of `σ` with `N(ū) = u` and `N(ūᵢ) = uᵢ` for the relative norm `N` from the fixed field of `σn` to that of `σ`, and that the relation `φ u − u = Σᵢ (τᵢ uᵢ − uᵢ)` holds in `A` (hypothesis `hstar`, with the action taken through chosen representatives). Then `N` of the correction term is zero.

## Proofs

The relative norm commutes with the action of `φ` and of each `τ i` (`relativeNorm_frobeniusFixedFieldAction`, from an earlier file), so the norm of the correction term is `(φ u − u) − Σᵢ (τᵢ uᵢ − uᵢ)`, which vanishes by `hstar`.

## Watch for

- `hstar` is the equation to be corrected and is a hypothesis; the theorem only computes the norm of the correction term and does not itself invoke the vanishing of `H⁻¹`.
- The action on `A` in `hstar` is through `Quotient.out` representatives of classes modulo inertia.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitCorrection.lean`: the Lean file is the source byte for byte (SHA-256 `909017d0aa02047b650a74306c1a823d8801fe9b92792c00d09d8c1927b1076a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
