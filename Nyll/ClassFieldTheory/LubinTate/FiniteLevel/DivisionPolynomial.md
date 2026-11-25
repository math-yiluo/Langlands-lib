# Standard Lubin–Tate division polynomials

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with valuation ring `O` and residue field of cardinality `q`, and let `π ∈ O`. The file defines over `O` the polynomial `f(X) = X^q + πX`, its compositional iterates, and the factors `Q_n(X) = f^(n)(X)^(q−1) + π`, and proves the purely polynomial factorization `f^(n+1) = f^(n) · Q_n`. Nothing here depends on the characteristic.

## Main definitions and results

- `standardLubinTatePolynomial F π`: the polynomial `X^q + πX`. It is monic of degree `q`, its value at `x` is `x^q + πx`, and as a power series it is the standard Lubin–Tate series (for a uniformizer `π`, the series of the bundled standard Lubin–Tate input).
- `standardLubinTatePolynomialIterate F π n`: the `n`-fold composite `f^(n)`, with `f^(0) = X` and `f^(n+1) = f ∘ f^(n)`. It is monic of degree `q^n` and vanishes at `0`.
- `standardLubinTatePrimitivePolynomial F π n`: the polynomial `Q_n = f^(n)^(q−1) + π`, monic of degree `(q − 1)·q^n`, with constant coefficient `π`.
- `standardLubinTatePolynomialIterate_succ_factor`: `f^(n+1) = f^(n) · Q_n`.

## Proof

Degrees and monicity follow from `q > 1` (the residue field is finite with at least two elements) and the degree of a composite. The factorization is the identity `y^q + πy = y·(y^(q−1) + π)` applied to `y = f^(n)`.

## Points to watch

- `π` is any element of `O` in most statements; only the comparison with the bundled series needs it to be a uniformizer.
- The file says nothing about roots, irreducibility of `Q_n`, or the Lubin–Tate extensions themselves.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`: the Lean file is the source byte for byte (SHA-256 `9820f70583e1adf32811b560e19961769f9ea3a0d5c15682e601d17ab20c4f2c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
