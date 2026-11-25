# The determinant norm under base change

Module `Nyll.ClassFieldTheory.Theorems.NormTheorems.TensorNormBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite field extension and A a nontrivial commutative K-algebra.

`tensorNorm_includeRight`: for y in L, the norm over A of 1 ⊗ y in A ⊗_K L (Mathlib's determinant norm `Algebra.norm A`) is the image in A of the field norm of y from L to K.

The proof chooses a K-basis of L, extends it to an A-basis of A ⊗_K L, and checks that the matrix of multiplication by 1 ⊗ y is the image of the matrix of multiplication by y, so the two determinants correspond.

The statement holds for the whole tensor algebra, whether or not it is a field. It needs no Galois hypothesis and no choice of a factor of A ⊗_K L; the only assumption on A is that it is nontrivial.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/NormTheorems/TensorNormBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `89424de87678f20943765378b97c7db5fd5327af33f32782a0ba0d8bb869ba21`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
