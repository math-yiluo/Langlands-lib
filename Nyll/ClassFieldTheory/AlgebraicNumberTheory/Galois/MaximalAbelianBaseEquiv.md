# Maximal abelian extensions along an isomorphism of fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given a ring isomorphism e : K ≃ M and a compatible isomorphism of algebraic closures, this file restricts it to the separable closures and then to the maximal abelian extensions K^ab and M^ab (the library's `maximalAbelianExtension`). It shows that the identification of Mathlib's abelianized absolute Galois group with Gal(K^ab/K) is compatible with these maps.

## Definitions

- `separableClosureEquivOfSemilinear e c hc`: the restriction of a compatible isomorphism c of algebraic closures to `SeparableClosure K ≃ SeparableClosure M`; `separableClosure_mem_semilinear` shows that c preserves separability, and `..._commutes` says the restriction extends e.
- `maximalAbelianExtensionEquivOfSemilinear e c hc`: the further restriction K^ab ≃ M^ab, for a compatible isomorphism c of separable closures; `..._commutes` again.
- `mathlibAbelianizationToMaximal K`: the isomorphism of topological groups from `Field.absoluteGaloisGroupAbelianization K` to Gal(K^ab/K), composed of the two comparisons from the separable model.
- `maximalAbelianExtensionBaseEquiv e`: K^ab ≃ M^ab built from `IsAlgClosure.equivOfEquiv`; `..._commutes` says it extends e.

## Results

- `maximalAbelianExtension_map_le`: c carries K^ab into M^ab.
- `mathlibAbelianizationToMaximal_mk`: on the class of σ, the comparison is restriction of σ to the separable closure and then to K^ab.
- `mathlibAbelianizationToMaximal_semilinear`: transporting a class along conjugation by c and then comparing equals comparing and then conjugating by the induced isomorphism of maximal abelian extensions.
- `mathlibAbelianizationToMaximal_baseEquiv`: the same square for `absoluteGaloisGroupAbelianizationEquivOfRingEquiv e` and `maximalAbelianExtensionBaseEquiv e`.

## Proof

That c maps K^ab into M^ab uses that the image of K^ab is abelian Galois over M, and that every abelian Galois intermediate field of the separable closure lies in the maximal abelian extension. Compatibility is checked on representatives σ by evaluating in the algebraic closure.

## Points to watch

- The containment of every abelian Galois intermediate field of the separable closure in K^ab, with no finiteness hypothesis, is proved here only as a private lemma (`abelianIntermediateField_le_maximalAbelianExtension`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/MaximalAbelianBaseEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `e087a7b75ed688adf92dd15c76aff6e024d9e489c3eeffebfb9ce32b6badc7cf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
