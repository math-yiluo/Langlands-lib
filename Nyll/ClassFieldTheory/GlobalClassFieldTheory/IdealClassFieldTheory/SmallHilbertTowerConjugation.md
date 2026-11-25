# Conjugation stability of the second small Hilbert class field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that in a two-step tower `F ⊆ L ⊆ M` of number fields over `ℚ`, where `L/F` is finite abelian and `M` is the small Hilbert class field of `L` (norm-subgroup quotient the ideal class group of `L`), every conjugate of `M` by an element of `Gal(F̄/F)` is `M` itself, so `M/F` is Galois. Fields are treated as fixed fields of closed subgroups of the automorphism group of `SeparableClosure ℚ`, inside the rational absolute idele-class formation `rationalIdeleClassRepresentation`.

## Abstract conjugation

For a group `G` with a topology and continuous multiplication, a `ℤ`-representation `A` and closed subgroups:

- `conjugateFiniteAbelianSubextensionField_eq_self`: a finite abelian subextension `L` of `K` is fixed by conjugation by any `s ∈ K`.
- `finiteNormSubgroup_map_conjugateFixed`: for `L ≤ K` of finite index and any `s ∈ G`, conjugation on fixed parts carries the relative norm subgroup of `(K, L)` onto that of the conjugate pair.
- `conjugateFiniteAbelianSubextensionOverBase L M s`: the conjugate of `M` (abelian over `L`) by `s ∈ K`, again over `L`; by `conjugateFiniteAbelianSubextensionOverBase_normSubgroup` its norm subgroup is the image of `M`'s under `stableBaseConjugationHom A L s`.

## The rational case

- `smallHilbertNormSubgroupInRationalClassFormation K`: the small Hilbert norm subgroup of the fixed field of `K`, carried into the fixed part of the class formation.
- `everywhereUnramifiedFiniteAbelianSubextension_le_smallHilbertClassField`: if `L` realizes this subgroup and `P` is a finite abelian subextension whose fixed-field extension satisfies `IsEverywhereUnramified`, then `P ≤ L`.
- `rationalSmallHilbertFixedPart_conjugation`: `stableBaseConjugationHom` is idele-class transport along the automorphism `smallHilbertBaseConjugationAutomorphism K L s` induced by `s⁻¹`.
- `smallHilbertNormSubgroupInRationalClassFormation_map_conjugation`: the small Hilbert subgroup is fixed by each such conjugation.
- `smallHilbertClassField_conjugateSubextension_eq_self` and `smallHilbertClassField_conjugate_eq_self`: if `M`'s norm subgroup equals the small Hilbert subgroup of `L`, the conjugate of `M` by any `s` in the base subgroup equals `M`.
- `smallHilbertClassFieldGaloisSubextension`: `M` as a finite Galois subextension over `K`, whose maximal abelian subextension contains `L`.
- `maximalAbelianSubextension_le_smallHilbertClassField_of_everywhereUnramified`: if `L` realizes the small Hilbert subgroup of `K` (`hL`) and `P` is finite Galois over `K` and everywhere unramified, its maximal abelian subextension is `≤ L`.

## Proofs

Conjugation stability combines the norm-subgroup transport with invariance of the small Hilbert subgroup under field automorphisms, then injectivity of the norm-subgroup map from finite abelian classification.

## Caveats

- The base field is a number field only as the fixed field of a closed subgroup over `ℚ`.
- "`M` is the small Hilbert class field" is the hypothesis `hM` (resp. `hL`), an equality of norm subgroups; existence is not established here.
- "Small Hilbert class field" is the library's name, tied to the ordinary ideal class group; unramifiedness uses the library's `IsEverywhereUnramified` and `IsUnramifiedAtInfinitePlaces`, and `≤` is the library's order on subextensions.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertTowerConjugation.lean`: the Lean file is the source byte for byte (SHA-256 `ac650c4c156e3946dd4d347c20c3f64fca79e004f5563b833fa3a6393d395700`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
