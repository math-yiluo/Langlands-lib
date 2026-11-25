# Artin reciprocity for the quadratic overextension at a ramified real place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.OverextensionArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite abelian extension of number fields and `v` an infinite place of `K` whose chosen place above it in `L` is ramified (hypothesis `hRamified`). The auxiliary quadratic extension `L(i)/K'`, where `K'` is the real fixed field of complex conjugation on `L(i)`, is built in earlier files. This file proves that, for `L(i)/K'`, the product of the library's chosen local Artin symbols, `globalArtinMonoidHom`, is trivial on principal ideles and agrees with the canonical global norm-residue map `globalNormResidueMonoidHom`.

## Main results

- `ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele`: `globalArtinMonoidHom` for `L(i)/K'` kills the principal ideles of `K'`.
- `ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom`: the induced map `IdeleClassGroup K' →* Gal(L(i)/K')`; it kills idele-class norms from `L(i)`.
- `ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom`: the induced map on `IdeleClassGroup K'` modulo the idele-class norms from `L(i)`, surjective and bijective.
- `ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one`: two non-identity elements of `Gal(L(i)/K')` are equal.
- `ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply` and `ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply`: these maps coincide with the global norm-residue equivalence and map.
- `globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_ideleClass_mk`: on the class of an idele `a` of `K'`, the global norm-residue map is `globalArtinMonoidHom a`.
- `globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass`: on the one-place class of `x` at an infinite place `w` of `K'`, it is the chosen local Artin symbol at `w`.
- `quotientLiftData`: a quotient lift packaged with its evaluation law.

## Proofs

Triviality on principal ideles: restriction from `Gal(L(i)/K')` to `Gal(ℚ(μ₄)/ℚ)` is injective, the Artin product is compatible with norm and restriction (`globalArtinMonoidHom_norm_restriction`), the norm of a principal idele is principal, and the product formula `rationalComplexificationGlobalArtin_principalIdele` for `ℚ(μ₄)/ℚ` holds. Bijectivity compares cardinalities with the global norm-residue equivalence. The agreement with that equivalence is then forced, since both maps are injective, send the trivial class to `1`, and the Galois group has at most one non-identity element.

## Caveats

- The results concern only this special extension `L(i)/K'`; the argument uses essentially that its Galois group has at most two elements.
- `globalArtinMonoidHom` is the library's own product of chosen local symbols and `chosenInfinitePlaceArtinMonoidHom w` is its chosen local symbol at an infinite place `w`; the file uses surjectivity of `globalArtinMonoidHom` and its triviality on idele norms from imported files.
- The file locally removes the instance `ramifiedInfinitePlaceRealFixedField_ratScalarTower`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/OverextensionArtin.lean`: the Lean file is the source byte for byte (SHA-256 `6366bfff1fc46975b4e6c9f2a5b215ea3abf914d6b949838dcdf607eab1c9545`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
