# Realizing the two-step small Hilbert class field tower

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` with small Hilbert class field `H₁` (the field whose norm subgroup has quotient the ideal class group), the file constructs the small Hilbert class field `H₂` of `H₁` as an actual subextension of `SeparableClosure ℚ` lying over the very closed subgroup that defines `H₁`, and packages `K ⊆ H₁ ⊆ H₂` as a finite Galois extension of `K`. Fields are fixed fields of closed subgroups of `Aut(SeparableClosure ℚ / ℚ)`, inside the rational absolute idele-class formation.

## Over a fixed middle field

Let `L` be a finite abelian subextension over a finite abstract field `K`, with fixed field `E`, and let `N = smallHilbertClassFieldNormAmbient E`, a finite Galois extension of `E` whose idele-class norm range lies in the small Hilbert subgroup.

- `smallHilbertTowerMiddleNormSubgroup K L`: the small Hilbert norm subgroup of `E`, carried into the fixed part of the class formation; `smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint` identifies it with the subgroup used in the conjugation file.
- `smallHilbertNormNeighborhoodEmbedding K L`: an embedding `N → SeparableClosure ℚ` whose restriction to `E` is the literal inclusion; `smallHilbertNormNeighborhoodEmbeddedBase_eq` says the fixing subgroup of the embedded `E` is `L.field`.
- `smallHilbertFiniteGaloisNormNeighborhood K L`: `N` as a finite Galois subextension over `L.field`; its abstract norm subgroup lies in the small Hilbert subgroup (`smallHilbertFiniteGaloisNormNeighborhood_normSubgroup_le`).
- `smallHilbertNormSubgroupInRationalClassFormation_isNormOpen`: hence the small Hilbert subgroup of `E` is open in the norm topology (`IsNormOpen`).
- `secondSmallHilbertClassFieldSubextension K L`: a finite abelian subextension over `L.field` whose norm subgroup is exactly this subgroup (`secondSmallHilbertClassFieldSubextension_normSubgroup`); `secondSmallHilbertClassFieldSubextension_ideleClassNorm_range` restates this as an equality of the idele-class norm range of its fixed field over `E` with `smallHilbertClassFieldNormSubgroup`.

## The actual tower

For a number field `K`, `smallHilbertTowerSecondSubextension K` applies the construction over `smallHilbertClassFieldSubextension K`, with exact norm subgroup `smallHilbertTowerSecondSubextension_normSubgroup`, and `smallHilbertTowerGaloisRealization K` is the whole tower as a finite Galois subextension of `smallHilbertClassFieldBaseSubgroup K`, obtained from the conjugation-stability result `smallHilbertClassFieldGaloisSubextension`.

## Proofs

The embedding of `N` is obtained by extending the composite embedding of `E` to an automorphism of `SeparableClosure ℚ` (`liftNormal`) and correcting by its inverse. Openness then gives the second stage through the existence half of finite abelian classification, `FiniteAbelianSubextension.normSubgroupMap_surjective`, for `rationalCyclotomicIdeleClassValuationData` and `rationalIdeleClassRepresentation_satisfiesClassFieldAxiom`.

## Caveats

- `secondSmallHilbertClassFieldSubextension` is defined by `Classical.choose`; only its norm subgroup is specified.
- The compatibility of the embedding with the first stage is essential: an unrelated copy of the middle field would give a class field over a conjugate subgroup.
- The file installs its own local `CommGroup` instance on `IdeleClassGroup F`, `smallHilbertTowerIdeleClassCommGroup`, the quotient structure by the principal ideles.
- "Small Hilbert class field" and `IsNormOpen` are the library's notions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertTowerRealization.lean`: the Lean file is the source byte for byte (SHA-256 `ae7dfb5acd301c237b8d9f4f41825d1e443cdb0300ec8ac90049f33693500abe`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
