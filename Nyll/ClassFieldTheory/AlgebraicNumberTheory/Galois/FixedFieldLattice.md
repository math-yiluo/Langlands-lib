# Fixed field of a join of subgroups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.FixedFieldLattice`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A single lattice fact from Galois theory, valid for any field extension Ω/k with no finiteness or Galois hypothesis.

- `IntermediateField.fixedField_sup_eq_inf`: for subgroups S and T of Gal(Ω/k), the fixed field of S ⊔ T is the intersection of the fixed fields of S and of T.

One inclusion holds because fixed fields reverse inclusion. For the other, an element fixed by S and by T has a stabilizer containing both, hence containing S ⊔ T.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/FixedFieldLattice.lean`: the Lean file is the source byte for byte (SHA-256 `a81898da2c4d97c3ecebbd81f0e2598eeed169c963f6f766051f049386b481e9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
