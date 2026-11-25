# Norms on fixed-field idele classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For closed subgroups `L ≤ K` of `Gal(ℚˢᵉᵖ/ℚ)`, with `L` normal in `K` and the fixed fields `F ⊆ E`, the file shows that the inclusion of fixed parts, the representation norm and the class-formation relative norm of `rationalIdeleClassRepresentation` become the ordinary inclusion and norm of idele classes for `E/F`.

## Main results

All three theorems assume `L` normal in `K` (normality of `extensionSubgroup K L hLK`), `K` of finite index in the whole group and `L` of finite index in `K`; then `E/F` is a finite Galois extension of number fields.

- `rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion`: the inclusion of the `K`-fixed part into the `L`-fixed part (`fixedFieldInclusion`) becomes `RelativeIdeleGroup.classInclusion F E`, the map from `C_F` into the relative idele class group of `E/F`.
- `rationalAbstractExtensionIdeleClassEquiv_norm`: the norm of the extension fixed representation (the sum over `K/L` of its action) becomes the relative idele-class norm `RelativeIdeleGroup.Cohomology.ideleClassNorm F E` followed by `classInclusion F E`.
- `rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm`: the class-formation `relativeNorm` from the `L`-fixed part to the `K`-fixed part, read in `C_F` through `rationalAbstractFixedFieldIdeleClassEquivFixed K`, is the relative idele-class norm of the element of `RelativeIdeleGroup.ClassGroup F E` given by `rationalAbstractExtensionIdeleClassEquiv`.

## Proofs

The inclusion statement follows the direct-limit image of a class through the four equivalences that make up `rationalAbstractExtensionIdeleClassEquiv`. The norm statement uses the action comparison of the companion action file, reindexes the sum over `K/L` by `Gal(E/F)`, and applies the imported formula expressing `classInclusion ∘ ideleClassNorm` as the product of Galois conjugates. The relative-norm statement combines both and cancels `classInclusion F E`, which is injective by an imported lemma.

## Points to watch

- The norm is `RelativeIdeleGroup.Cohomology.ideleClassNorm F E`, defined on the library's relative presentation `RelativeIdeleGroup.ClassGroup F E` of the idele classes of `E`, with values in `IdeleClassGroup F`.
- Nothing is stated for a pair `L ≤ K` with `L` not normal in `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitExtensionNorm.lean`: the Lean file is the source byte for byte (SHA-256 `8b86b4fba2ca87597fad2e8f5c99e70987e18b42fcefd3123e05e66ba64bd985`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
