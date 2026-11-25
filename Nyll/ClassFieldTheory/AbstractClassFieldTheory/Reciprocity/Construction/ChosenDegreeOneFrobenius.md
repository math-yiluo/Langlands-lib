# A chosen Frobenius element of degree one

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ChosenDegreeOneFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be an abstract field of finite residue degree and `G_L` a closed normal subgroup of `G_K`. Because the normalized degree `d_K : G(L̃|K) → ℤ̂` is surjective, some element has normalized degree `1`. The file fixes one such element as a Frobenius element of exponent one, keeping the choice and its property together for the later proof of multiplicativity.

- `DegreeData.chosenDegreeOneFrobeniusElement`: an element of `FrobeniusElements K L hLK` with `d_K = 1`, obtained by choice from surjectivity of `extensionNormalizedDegreeContinuous`.
- `DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement`: its Frobenius exponent is `1`.

The element is a noncanonical choice (`Classical.choose`); only its normalized degree is specified.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ChosenDegreeOneFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `290039295149ad8aadfed43e908d2e64f78ac5dd2a61e3568a150d9bddae48b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
