# Ideles in the idèle-class norm quotient

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension of number fields `L / K`, this file defines the map from ideles of `K` to the norm quotient of `C_K` by the range of the norm `C_L → C_K`, used by the global norm residue symbol constructions.

- `globalNormClassFromIdele K L`: the composite of the quotient map `I_K → C_K` by the principal ideles and the quotient map by the range of the idèle-class norm `ideleClassNorm K L`.
- `globalNormClassFromIdele_principalIdele`: it sends every principal idele to `1`.

No Galois hypothesis is made on `L / K`. `C_K` is the library's own `IdeleClassGroup K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/NormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `be6b06c7e42fbe175dcf0030f2e908770f9ec1395faf10ebfe7623b973db279b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
