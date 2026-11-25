# Restricting the cyclotomic Artin map to a finite unramified layer

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H : FiniteAbstractField` be a closed finite-index subgroup of Gal(ℚ̄/ℚ) (with ℚ̄ = `SeparableClosure ℚ`), F its fixed field, and `L : FiniteAbelianSubextension H.field` a finite abelian subextension with fixed field E. Let U be the fixed field of the cyclotomic inertia subgroup, the abstract maximal unramified extension of F. For L unramified for the cyclotomic degree datum, the file builds the restriction Gal(U/F) → Gal(E/F) and shows that, composed with the cyclotomic idele-class Artin map, it gives the global norm-residue map C_F → Gal(E/F).

## Main definitions and results

- A local instance makes the fixed field F a `NumberField`.
- `abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom H L hUnramified`: the restriction Gal(U/F) →* Gal(E/F). It is defined as a composite of coordinate changes: Gal(U/F) ≃ ZHat (`abstractFixedFieldCyclotomicGalEquivZHat`), then the inverse of the maximal-unramified degree equivalence, then the abstract finite unramified restriction `DegreeData.finiteUnramifiedRestriction`, then the identification of the abstract quotient with Gal(E/F). Its `_apply` lemma unfolds it by `rfl`.
- `abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of` (simp): the abelianized quotient comparison sends the class of a quotient element to the matching automorphism of E.
- `abstractFixedFieldCyclotomicFiniteRestriction_ideleClassArtin_fixed` and `abstractFixedFieldGlobalNormResidueMonoidHom_fixed_eq_finiteUnramifiedRestriction`: on a class written through the fixed-part coordinate, both the restricted cyclotomic Artin symbol and the global norm-residue value equal the finite restriction of `maximalUnramifiedNormResidueSymbol`.
- `abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction`: for every idele class c of F, `abstractFixedFieldGlobalNormResidueMonoidHom H L c` equals the restriction of `abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c`.

## Proof

Each class c is transported to the fixed part of the rational idele-class representation. There the cyclotomic Artin symbol agrees with the maximal-unramified norm-residue symbol (imported `abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue`). The norm-residue symbol of a finite norm class is the restriction of that symbol (`normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction`). The two identifications are then joined.

## Points to watch

- "Unramified" in `hUnramified` is the abstract class-formation notion relative to `rationalCyclotomicDegreeData`, not unramifiedness at the primes of F. Likewise U is the abstract maximal unramified extension cut out by the cyclotomic degree datum.
- The "genuine restriction" is built from quotient coordinates, not from Mathlib's `AlgEquiv.restrictNormalHom`; this file does not relate the two.
- The main identity holds only for L unramified in that sense.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicUnramifiedRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `470d23471056194d3ce9568c465529350860332649c0df918203528c8ee2a97f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
