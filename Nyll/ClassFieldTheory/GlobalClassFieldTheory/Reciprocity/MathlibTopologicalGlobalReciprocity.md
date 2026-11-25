# Topological global reciprocity in Mathlib's groups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` in any universe, this file restates the library's maximal-abelian Artin isomorphism with Mathlib's idèle class group and Mathlib's abelianised absolute Galois group.

- `mathlibIdeleClassConnectedQuotientEquivAbelianization K`: an isomorphism of topological groups from `IdeleClassConnectedQuotient K`, the idèle class group modulo its identity component, onto `Field.absoluteGaloisGroupAbelianization K`. It composes the comparison of idèle class groups, `ideleClassComponentQuotientEquivMaximalAbelianGalois`, and the identification of the abelianised absolute Galois group with `Gal(Kᵃᵇ / K)`.
- `mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K`: the same kind of isomorphism, transported from the small model `Shrink.{0} K`.
- `mathlibGlobalArtin K`: the quotient map followed by the transported isomorphism, a continuous homomorphism; it is surjective and its kernel is the identity component (`mathlibGlobalArtin_ker`).

## Remarks

- The public map is defined through the small-model transport. The equality of that transport with the native isomorphism, and the finite projections of the public map, are proved in `MathlibGlobalArtinNaturality`, not here.
- The normalisation is that of the library's maximal-abelian construction, called geometric in the comments.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MathlibTopologicalGlobalReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `4a25f47e4c5851630e5a0e8c4b9fef0c4e37bd1488d35da669c6466898a34400`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
