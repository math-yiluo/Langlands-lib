# Eisenstein property of the standard primitive division polynomials

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a local field with uniformizer π and residue field of q elements, and f(X) = X^q + π·X. The file shows that the primitive quotient polynomial Qₙ(X) = (f^[n](X))^(q−1) + π over the valuation ring is Eisenstein, hence irreducible, in any characteristic.

## Main results

- `standardLubinTatePolynomial_map_residue`, `standardLubinTatePolynomialIterate_map_residue`: modulo the maximal ideal, f reduces to X^q and its n-fold iterate to X^(q^n).
- `standardLubinTatePrimitivePolynomial_map_residue`: Qₙ reduces to X^((q−1)·q^n).
- `standardLubinTatePrimitivePolynomial_isEisensteinAt`: Qₙ is Eisenstein at the maximal ideal.
- `standardLubinTatePrimitivePolynomial_isPrimitive`: Qₙ is primitive (it is monic).
- `standardLubinTatePrimitivePolynomial_irreducible`: Qₙ is irreducible over the valuation ring.

## Proofs

Monicity, the degree and the shape of Qₙ come from the division-polynomial file. The lower coefficients vanish modulo the maximal ideal because the reduction is a monomial, and the constant coefficient π is not in m². Mathlib's Eisenstein criterion then gives irreducibility, using q > 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`: the Lean file is the source byte for byte (SHA-256 `8d63f2fb102d45d37fc342ed76f49f63882e30251c05c82d50a3c55c51c16d4d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
