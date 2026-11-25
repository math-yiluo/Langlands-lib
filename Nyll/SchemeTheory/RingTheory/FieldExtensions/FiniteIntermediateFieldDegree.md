# A finite Galois subextension of each degree in an algebraic closure of a finite field

Module `Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite field `k`, an algebraically closed field `Ω` containing `k`, and a positive integer `n`, the file embeds Mathlib's degree-`n` extension `FiniteField.Extension k p n` (with `p` the characteristic of `k`) into `Ω` and shows that its image is a finite Galois intermediate field of `Ω/k` of degree `n`.

- `finiteResidueBaseRingCharPrime`: the characteristic of a finite field is prime (used as a local instance).
- `finiteResidueExtensionEmbeddingInto k Ω n`: a `k`-embedding of the degree-`n` extension into `Ω`, chosen by `IsAlgClosed.lift`.
- `finiteResidueIntermediateFieldIn k Ω n`: its image, and `finiteResidueExtensionEquivIntermediateIn`, the isomorphism of the model with that image.
- `finiteResidueGaloisIntermediateFieldIn k Ω n`: the image as a `FiniteGaloisIntermediateField`.
- `finrank_finiteResidueGaloisIntermediateFieldIn`: its degree over `k` is `n`.

The subfield is defined through a chosen embedding; its independence of the choice, and the uniqueness of the degree-`n` subfield, are not proved here. `n` is required to be nonzero through `NeZero n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/SchemeTheory/RingTheory/FieldExtensions/FiniteIntermediateFieldDegree.lean`: the Lean file is the source byte for byte (SHA-256 `00e9190b90255fc38ea359d192cd025a02d57198dde932dbdda3089156627009`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
