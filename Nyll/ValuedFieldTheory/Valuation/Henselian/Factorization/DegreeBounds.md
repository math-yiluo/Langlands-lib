# Degree bounds in the Hensel iteration

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Degree estimates for the approximation proof of Hensel's lemma, where the error `f − g h` is written as `πⁿ · fₙ`.

- `henselFactorization_natDegree_eq_of_residue_eq_of_le`: over a local ring, if `deg P ≤ m`, `P` reduces to `ḡ`, `deg ḡ = m` and `ḡ` has nonzero leading coefficient, then `deg P = m`.
- `henselFactorization_residual_right_natDegree_le`: over a field, if `f̄ = ḡ h̄`, `deg f̄ ≤ d`, `deg ḡ = m` and `ḡ ≠ 0`, then `deg h̄ ≤ d − m`.
- `henselFactorization_error_natDegree_le`: if `deg f ≤ d`, `deg g ≤ m`, `deg h ≤ d − m` and `m ≤ d`, then `deg (f − g h) ≤ d`.
- `henselFactorization_error_factor_natDegree_le`: under the same bounds, over a ring without zero divisors, if `f − g h = πⁿ · fₙ` with `πⁿ ≠ 0`, then `deg fₙ ≤ d`; `henselFactorization_error_factor_residue_natDegree_le` gives the same bound for the reduction of `fₙ` over a local ring.
- Helpers: reduction does not raise degree; without zero divisors, dividing by a nonzero constant keeps a degree bound.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/DegreeBounds.lean`: the Lean file is the source byte for byte (SHA-256 `22f1347f516398e0197d88170d1acc96fedceca3402bdc08370b698d2011091c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
