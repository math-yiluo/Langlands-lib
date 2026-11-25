# Embedded abelian extensions as abstract abelian subextensions

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.EmbeddedAbelianSubextension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's abstract class field theory works with closed subgroups of Gal(ℚ̄/ℚ), where ℚ̄ is `SeparableClosure ℚ`. A finite abelian extension of a subgroup B is described by an open subgroup of B. This file converts a concrete finite abelian extension E/K of number fields, embedded in ℚ̄, into such an abstract object.

- `numberFieldEmbeddedAbelianSubextension K E j B hbase`: given an embedding `j : E →ₐ[ℚ] SeparableClosure ℚ` and a closed subgroup B equal to the fixing group of the image of K (hypothesis `hbase`), a `FiniteAbelianSubextension B`. Its underlying finite Galois subextension is the imported `numberFieldEmbeddedFiniteGaloisSubextension`. Commutativity of its Galois quotient is transported from Gal(E/K) along the imported isomorphism `numberFieldEmbeddedExtensionQuotientEquivGaloisGroup`.
- `numberFieldEmbeddedAbelianSubextension_field`: the top subgroup of this subextension is the fixing group of j(E).

## Points to watch

- The base subgroup B is passed separately, with only a propositional equality to the fixing group of K. This lets a subgroup chosen elsewhere be used without rewriting the definition.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/EmbeddedAbelianSubextension.lean`: the Lean file is the source byte for byte (SHA-256 `530c993b89dc5a4dd6869a272beb1a1521ce45fc2942011687f74b42d149bc83`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
