# The field-of-norms equivalence of categories

Module `FontaineWintenberger.FieldOfNorms.Relative.Equivalence`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` an infinite separable APF extension. The file assembles Wintenberger's Theorem 3.2.2: the construction `M ↦ RelFieldOfNorms K L M` is an equivalence from the category of separable algebraic extensions of `L` to the category of separable algebraic extensions of the norm field `FieldOfNorms K L`. Both categories are instances of `SeparableExtensionCat`, the full subcategory of commutative algebras that are fields and separable over the base.

## Main definitions

* `RelFieldOfNorms.objectOf M`: for a separable field extension `M` of `L`, the object of `SeparableExtensionCat (FieldOfNorms K L)` given by `RelFieldOfNorms K L M`; `RelFieldOfNorms.objectMapOf t` is the morphism given by `RelFieldOfNorms.algMap` of an `L`-embedding `t`.
* `RelFieldOfNorms.obj`, `RelFieldOfNorms.objMap`: the same on objects and morphisms of `SeparableExtensionCat L`. For an object `A`, the `K`-algebra structure on its underlying field is the composite through `L`.
* `RelFieldOfNorms.functor`: the resulting functor.
* `RelFieldOfNorms.functorFullyFaithful`: a `Functor.FullyFaithful` structure for it.
* `RelFieldOfNorms.objectFiniteAlgEquiv`: for `M/L` finite, the underlying algebra of `objectOf M` is isomorphic over `FieldOfNorms K L` to `FieldOfNorms K M`.
* `RelFieldOfNorms.objectIso`: an algebra isomorphism from `RelFieldOfNorms K L M` to the field underlying an object `B` gives an isomorphism `objectOf M ≅ B`.
* `RelFieldOfNorms.equivalence`: the equivalence of categories, whose functor is `RelFieldOfNorms.functor` (`RelFieldOfNorms.equivalence_functor`).

## Main results

* `RelFieldOfNorms.objectMapOf_id`, `objectMapOf_comp`: functoriality.
* `RelFieldOfNorms.objectMapOf_bijective`, `RelFieldOfNorms.objMap_bijective`: the map on morphisms is bijective (Theorem 3.2.2(ii)).
* `RelFieldOfNorms.objectMapOf_valuation`: the induced maps preserve `RelFieldOfNorms.valuation`.
* `RelFieldOfNorms.functorEssSurj`: every separable algebraic extension of `FieldOfNorms K L` is isomorphic to a value of the functor.
* `RelFieldOfNorms.functorIsEquivalence`: the functor is an equivalence.

## Proofs

The file is an assembly. Bijectivity on morphisms is `RelFieldOfNorms.algMap_bijective` from `FontaineWintenberger.FieldOfNorms.Relative.Hom`. Essential surjectivity is `exists_relFieldOfNorms_algEquiv` from `FontaineWintenberger.FieldOfNorms.Relative.EssImage`, which realizes any separable algebraic extension of the norm field as `RelFieldOfNorms K L M` for an intermediate field `M` of `SeparableClosure L`; `RelFieldOfNorms.functor_mem_essImage_of_algEquiv` replaces `M` by a universe-lifted copy using `RelFieldOfNorms.congr`.

## Remarks

* Universes: with `K : Type u` and `L : Type v`, both categories consist of extensions living in `Type (max u v w)`; the extra parameter `w` is free. The universe lift in the proof of essential surjectivity is what reconciles this with `SeparableClosure L : Type v`.
* The fully faithful structure and the equivalence are obtained by choice from the bijectivity statements; no explicit inverse functor is constructed.
* The equivalence is stated for the categories of fields with algebra maps; compatibility with valuations is recorded only as preservation of `RelFieldOfNorms.valuation` by the induced maps.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, Theorem 3.2.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/Equivalence.lean` (SHA-256 of the source file `5fbe338e37d1e955266e1646274ee4ddb1dd54bd5c05d00f2f880204640bbce8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
