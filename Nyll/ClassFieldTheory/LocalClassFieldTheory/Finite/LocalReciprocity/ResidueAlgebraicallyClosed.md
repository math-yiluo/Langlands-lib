# Residue fields of algebraically closed valued fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file proves that the residue field of any valuation ring of an algebraically closed field is algebraically closed, and that pulling a valuation ring back along a purely inseparable extension gives a purely inseparable residue extension. Both are used to apply the degree map of finite fields to the residue field of the separable closure of a local field.

## Main definitions and results

- `valuationSubring_residueField_isAlgClosed`: for a valuation ring `A` of an algebraically closed field `Ω`, the residue field of `A` is algebraically closed. A monic irreducible residue polynomial is lifted to a monic polynomial over `A`; a root in `Ω` is integral over `A`, hence in `A`, and its residue is a root.
- `valuationSubringComapMap`, `valuationSubringComapMap_isLocalHom`, `valuationSubringComapResidueMap`: for a field extension `Ω/F` and a valuation ring `A` of `Ω`, the inclusion of the pullback of `A` to `F` into `A` is a local homomorphism, and the induced map of residue fields.
- `valuationSubring_comap_residueField_isPurelyInseparable`: if `Ω/F` is purely inseparable, so is the residue extension of the pullback of `A` into the residue field of `A`. In characteristic `p`, a `p`-power of each element lies in `F`; in characteristic zero the extension is trivial.

## Points to watch

`F` and `Ω` are taken in the same universe in the second part.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean`: the Lean file is the source byte for byte (SHA-256 `d3241fc70729081a03f3d6f7af8532e48d77f851baf30125617101f651603ba2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
