# Principal ideles and the idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file defines the diagonal embedding of Kˣ into the idele group and the idele class group C_K = I_K / Kˣ.

- `IdeleGroup.principalIdele K`: the homomorphism Kˣ → `IdeleGroup K`. It is the map to the units of Mathlib's adele ring, followed by the identification `equivAdeleRingUnits` of those units with the library's idele group.
- `finiteComponent_principalIdele` and `infiniteComponent_principalIdele`: each component of the principal idele of x is the image of x in the completion.
- `principalIdele_injective`: the diagonal map is injective.
- `IdeleGroup.principalSubgroup K`: its image. `principalEquiv K` is the isomorphism from Kˣ onto it, and `coe_principalEquiv` gives its value.
- `IdeleClassGroup K`: the quotient of `IdeleGroup K` by the principal subgroup, declared as an abbreviation.

## Points to watch

- `IdeleGroup K` is the library's own type, not the units of Mathlib's adele ring. The two are identified through `equivAdeleRingUnits`, from the imported `Idele.Basic`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/PrincipalCore.lean`: the Lean file is the source byte for byte (SHA-256 `2b8b5392f7def380bd2eadc5e0785870a34512d9ac38ccae763298070e3fb5b4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
