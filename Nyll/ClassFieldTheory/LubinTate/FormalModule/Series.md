# Lubin–Tate power series

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Series`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field K with residue field of q elements and an element π of its valuation ring, the file defines a Lubin–Tate series for π: a one-variable power series over the valuation ring with zero constant coefficient, linear coefficient π, and reduction modulo the maximal ideal equal to X^q.

## Main definitions

- `LubinTateSeries F π`: a structure with fields `toPowerSeries`, `constantCoeff_eq_zero`, `coeff_one_eq_uniformizer` (the linear coefficient is π) and `map_residue_eq_frobenius` (the coefficientwise reduction is X^q, with q = `Nat.card F.residueField`). The three properties are simp lemmas.

## Main results

- `LubinTateSeries.ext`: two Lubin–Tate series are equal when their underlying power series are.

## Watch for

- π is not required to be a uniformizer in the structure; that hypothesis is added where needed. For a uniformizer this is the usual class of series f ≡ πX modulo degree 2 with f ≡ X^q mod π.
- `LocalField` is the library's own structure, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/Series.lean`: the Lean file is the source byte for byte (SHA-256 `ec526de4a9cc8d83a79eab4cb99920c2a124110bfed573e273f144e55daaa947`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
