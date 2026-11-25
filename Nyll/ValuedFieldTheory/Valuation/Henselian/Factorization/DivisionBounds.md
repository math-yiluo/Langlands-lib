# Degree bound for the remainder in the Hensel correction step

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the correction step of the approximation proof of Hensel's lemma, a polynomial is divided by a lift `g₀` of a residual factor, giving a remainder `p` with `deg p < deg g₀`. The file turns this into the bound used later.

- `henselFactorization_remainder_natDegree_le_of_degree_lt`: if `g₀` has natural degree `m` and `deg p < deg g₀`, then `p` has natural degree at most `m`.
- `henselFactorization_residue_remainder_natDegree_le_of_degree_lt`: over a local ring, under the same hypotheses, the reduction of `p` modulo the maximal ideal also has natural degree at most `m`.

The conclusion is the non-strict bound `≤ m` on natural degrees, whereas the hypothesis `deg p < deg g₀` is a strict inequality of degrees.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/DivisionBounds.lean`: the Lean file is the source byte for byte (SHA-256 `e3d844ee38653e8d08c2ee5ac4125759384ff0e3fa9753633b3e6b43138b7ac5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
