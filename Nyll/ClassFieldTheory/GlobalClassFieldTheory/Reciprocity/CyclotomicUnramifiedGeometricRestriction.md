# Unramified layers inside the cyclotomic unramified field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedGeometricRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The setting is abstract class field theory over ℚ, with the cyclotomic degree datum `rationalCyclotomicDegreeData`. For a finite abstract field `H` with fixed field F, let U be the fixed field of the cyclotomic inertia of `H`, the "maximal unramified" field. Let L be a finite abelian subextension of `H` that is unramified in the abstract sense, with fixed field E. The file shows that E lies in U, that the restriction Gal(U/F) → Gal(E/F) defined on quotient presentations is ordinary restriction of field automorphisms, and that it carries the infinite Artin symbol to the finite one.

## Main definitions and results

- `abstractFixedFieldCyclotomicFiniteUnramifiedField_le`: if `L` is unramified for `rationalCyclotomicDegreeData`, then E ≤ U.
- `abstractFixedFieldCyclotomicFiniteUnramifiedInclusion`: the inclusion E → U as an F-algebra map. The induced algebra structure and scalar action are named definitions (`...InclusionAlgebra`, `...InclusionSMul`), and `...InclusionScalarTower` is a theorem: F ⊆ E ⊆ U is a scalar tower for them.
- `abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom`: the restriction `abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom`, defined in another file through the degree datum and quotient groups, equals `AlgEquiv.restrictNormalHom E`.
- `abstractFixedFieldCyclotomicFiniteRestriction_infiniteGlobalArtinMonoidHom`: for an idele a of F, this restriction sends `infiniteGlobalArtinMonoidHom F U a` to `globalArtinMonoidHom` of E/F at a.

## Proofs

Containment uses the characterization of unramified extensions by inertia (`isUnramified_iff_inertia_le`). The restriction identity is checked on representatives τ of the quotient: for each x in E, both sides send x to τ(x), compared in `SeparableClosure ℚ`. It uses the ℤ̂ coordinate `abstractFixedFieldCyclotomicGalEquivZHat` and `DegreeData.finiteUnramifiedRestriction_mk`. The Artin statement then follows from the general compatibility of the infinite Artin map with restriction in a scalar tower.

## Watch for

- "Unramified" and "maximal unramified" are meant in the sense of the abstract degree datum, not of ramification of primes.
- The ℚ-algebra structure on `SeparableClosure ℚ` is fixed locally as `DivisionRing.toRatAlgebra`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicUnramifiedGeometricRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `b246ae5e1f69954b20b0f22893c69a893b69196f5447911a25ce0bef1de39c86`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
