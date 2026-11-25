# Idele-class norms from the normal closure

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L/K` of number fields, every idele-class norm from the normal closure of `L/K` is already a norm from `L`.

- `finiteNormalClosure_ideleClassNorm_range_le_source`: the image of `ideleClassNorm K (finiteNormalClosure K L)` in `C_K` is contained in the image of `ideleClassNorm K L`.

The proof views the distinguished copy `finiteNormalClosureOriginalField K L` of `L` as an intermediate field of the normal closure, applies norm transitivity in the tower (`ordinaryIdeleClassNorm_range_le_of_tower`), passes to relative coordinates (`ordinaryIdeleClassNorm_range_eq_relative`), and transports the norm subgroup back to `L` along the algebra isomorphism `finiteNormalClosureOriginalFieldEquiv K L` (`ideleClassNorm_range_algEquiv`).

The normal closure `finiteNormalClosure K L` and the copy of `L` inside it are defined in an imported file. According to the file, the result provides a finite Galois norm subgroup inside the norm subgroup of an arbitrary finite extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/NormalClosureNorm.lean`: the Lean file is the source byte for byte (SHA-256 `abf133a47c6849fdb7cbcac20fa4b25db8275264d4ec2a13100a7fce32dc07a7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
