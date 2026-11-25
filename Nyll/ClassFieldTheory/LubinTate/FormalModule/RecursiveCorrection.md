# One step of the recursive correction of a Lubin–Tate intertwiner

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let π be a uniformizer of a local field K, e and ē Lubin–Tate series for π, and H a power series in finitely many variables with prescribed linear term L. For a multi-degree d of total degree at least 2, the file adds to H the monomial c·X^d, with c the correction coefficient of the recursive-coefficient file, and shows that this kills the degree-d coefficient of the intertwining defect while keeping the linear term.

## Main definitions

In `LubinTate.SameUniformizer`:

- `monomialCorrection hπ e ebar hH d hd`: the monomial c·X^d.
- `correctedIntertwiner hπ e ebar hH d hd`: H + c·X^d.

## Main results

- `correctedIntertwiner_hasLinearTerm`: the corrected series still has linear term L.
- `coeff_defect_correctedIntertwiner_eq_zero`: its defect has zero coefficient at d.

## Proofs

By the degree-stabilization file, adding c·X^d raises the degree-d defect coefficient by π·(1 − π^(|d|−1))·c, which by the choice of c is minus the old coefficient.

## Watch for

- One step cancels one coefficient only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCorrection.lean`: the Lean file is the source byte for byte (SHA-256 `420664019e9ea6dcb936f34e877db37ed5ef53fbeec3f5554094d25c7402e9d0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
