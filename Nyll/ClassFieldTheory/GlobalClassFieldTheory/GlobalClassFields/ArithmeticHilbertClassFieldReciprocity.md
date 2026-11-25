# Arithmetic reciprocity for the Hilbert class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticHilbertClassFieldReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, the library selects a big (narrow) Hilbert class field `bigHilbertClassField K` and a small (ordinary) one `smallHilbertClassField K`. This file identifies their Galois groups with the narrow class group and the ideal class group. Arithmetic global reciprocity is composed with the identification of the Hilbert norm quotient of `C_K` with the class group, and the resulting map is evaluated on ideles. Following the docstring, the ideal-theoretic Artin map uses arithmetic Frobenius, so the arithmetic normalization is used throughout.

## Main results

- `arithmeticReciprocity_quotientTransport_trans_globalNormResidue`: for a finite abelian `E / F` with `N C_E = H` and any group isomorphism `f : C_F ⧸ H ≃* A`, reciprocity followed by `f` sends the norm-residue symbol of `c` to `f (c mod H)`.
- `arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal`: `Gal(H⁺ / K) ≃* RayClass.NarrowClassGroup K`. Its `_globalNormResidue` lemma evaluates it on norm-residue symbols; `_idele` shows the symbol of the class of an idele `a` goes to the narrow ideal class of `a`.
- `arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal`: `Gal(H / K) ≃* ClassGroup (𝓞 K)`, with the analogous lemmas; the symbol of an idele `a` goes to its ideal class `IdeleGroup.idealClass a`.
- `arithmeticBigHilbertClassFieldReciprocityData`, `arithmeticSmallHilbertClassFieldReciprocityData`: each isomorphism bundled with its evaluation law.

## Points to watch

- These are only group isomorphisms (`MulEquiv`); no continuity is stated for them, although the reciprocity factor is a `ContinuousMulEquiv`.
- The Hilbert class fields are specific selected fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ArithmeticHilbertClassFieldReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `6e13722dfd0e0ef37ff77f4ffc22c32c574808570d64eed64c9064255e90e08f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
