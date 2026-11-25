# The category of separable algebraic field extensions

Module `FontaineWintenberger.FieldOfNorms.Relative.Category`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a field `R`, the file defines the category of separable algebraic field extensions of `R` as a full subcategory of Mathlib's category `CommAlgCat R` of commutative `R`-algebras. It contains definitions only.

* `separableFieldProperty R`: the property of an object `A` of `CommAlgCat R` that `A` is a field (`IsField A`) and `Algebra.IsSeparable R A`.
* `SeparableExtensionCat R`: the full subcategory on the objects with this property.
* `SeparableExtensionCat.of E`: the object given by a field `E` with a separable `R`-algebra structure.
* `SeparableExtensionCat.homEquiv A B`: the bijection between morphisms `A ⟶ B` and `R`-algebra homomorphisms of the underlying algebras.
* `SeparableExtensionCat.isoOfAlgEquiv e`: the isomorphism of objects given by an `R`-algebra isomorphism `e : E ≃ₐ[R] F`.

`Algebra.IsSeparable` is Mathlib's notion: every element is separable over `R`, so the extensions are algebraic but may be infinite. All objects of one category live in a fixed universe `v`, independent of the universe `u` of `R`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/Category.lean` (SHA-256 of the source file `383e21f4ef8cc5b7f09eaad8aede8a3db194deeac151fcd8b710cba88d8ca2b6`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
