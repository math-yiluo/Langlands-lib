# Index of the norm group of a standard Lubin–Tate level

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field K whose residue field has q elements, and a uniformizer π of `standardLocalField K`, the file computes the index of the norm group of the n-th standard Lubin–Tate level L_n: it is (q − 1) · q^n.

## Main results

- `standardLubinTateNormSubgroup_index`: for any uniformizer π, the index of `standardLubinTateNormSubgroup hπ n` in K^× is (q − 1) · q^n.
- `standardLubinTateCanonicalNormSubgroup_index`: the same for the canonical uniformizer, with the proof `standardLocalFieldUniformizer_isUniformizer K` that it is a uniformizer in place of `hπ`.

## Proof

By finite local reciprocity the norm quotient of the finite abelian extension L_n/K has [L_n : K] elements (`card_normQuotient_eq_finrank_of_isAbelianGalois`), and [L_n : K] = (q − 1) · q^n by the degree formula for standard levels.

## Caveats

The index is obtained from local reciprocity and the degree of L_n, not by computing the norm group directly.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardNormIndex.lean`: the Lean file is the source byte for byte (SHA-256 `c71e5f8703ececb1cbbb2b08024d6530b16f492b689759fea5fc78278a87e39c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
