# Arithmetic normalization of global reciprocity

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

According to the file's header, the library's local class formation takes as valuation the logarithm of the absolute value, so its element of valuation one is the inverse of a uniformizer, and the resulting reciprocity map sends a uniformizer to geometric Frobenius. This file defines the arithmetic normalization, in which a uniformizer goes to arithmetic Frobenius, by composing the global norm-residue maps and the chosen Artin maps with inversion of the target, and restates the known properties in this normalization.

## Finite Galois extensions

For `L/K` finite Galois:

- `commutativeGroupInversionContinuousMulEquiv G`: inversion as a topological group automorphism of a commutative topological group.
- `arithmeticGlobalNormResidueAbelianizationMonoidHom K L : C_K →* Gal(L/K)ᵃᵇ`, the pointwise inverse of `globalNormResidueAbelianizationMonoidHom`; it is surjective and its kernel is the range of `ideleClassNorm K L`.
- `arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv`: the topological isomorphism `IdeleClassGroup K ⧸ (ideleClassNorm K L).range ≃ₜ* Gal(L/K)ᵃᵇ`, and `arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv`, its inverse, in the direction from `Gal(L/K)ᵃᵇ` to that quotient.

## Finite abelian extensions

For `L/K` finite abelian:

- `arithmeticGlobalNormResidueMonoidHom K L : C_K →* Gal(L/K)`: surjective, continuous, with kernel the norm range.
- `arithmeticGlobalNormResidueContinuousMulEquiv` and `arithmeticGlobalReciprocityContinuousMulEquiv`: the corresponding topological isomorphisms, with simp lemmas relating them to the symbol on idele classes.
- `arithmeticChosenFinitePlaceArtinMonoidHom` and `arithmeticChosenInfinitePlaceArtinMonoidHom`: inverses of the library's chosen local Artin maps at finite and infinite places.
- `arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass` and `..._comp_infinitePlaceIdeleClass`: local-global compatibility; restricted to the units of one completion, the global map is the local one.
- `arithmeticGlobalArtinMonoidHom K L`: the idele-level Artin map, inverse of `globalArtinMonoidHom`; it is trivial on principal ideles, agrees with the local maps on one-place ideles, and descends to `arithmeticGlobalNormResidueMonoidHom`.

## Proofs

Every result is the corresponding result for the geometric maps, composed with inversion; this is legitimate because the targets are commutative.

## Caveats

- The statements about Frobenius are in the file's comments only: no theorem here evaluates any of these maps on a uniformizer.
- The unprefixed maps (`globalNormResidueMonoidHom`, `chosenFinitePlaceArtinMonoidHom`, ...) are, per this file, in geometric normalization; the `arithmetic` maps are pointwise their inverses.
- The topology on `Gal(L/K)ᵃᵇ` is the quotient topology fixed by the topological reciprocity file, installed here as a local instance.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean`: the Lean file is the source byte for byte (SHA-256 `e612dc71f90196d3b76fd634b3a3d2acb05c464cecb1c3dbbc057f72ab197c9b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
