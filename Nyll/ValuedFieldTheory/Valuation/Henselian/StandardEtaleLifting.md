# Lifting points of standard étale algebras over a henselian pair

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.StandardEtaleLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a commutative ring R and an ideal I such that (R, I) is a henselian pair (Mathlib's `HenselianRing R I`), this file shows that R-algebra maps from a standard étale algebra to R/I lift to R.

- `exists_standardEtale_lift`: for a standard étale pair P (Mathlib's `StandardEtalePair R`, with monic polynomial f and denominator g), every R-algebra map σ from P's algebra to R/I is the reduction of an R-algebra map τ to R.
- `exists_isStandardEtale_lift`: the same for any R-algebra S that is standard étale (`Algebra.IsStandardEtale R S`), using a chosen standard étale presentation.

## Proof

Lift the image of X to a₀ ∈ R. Then f(a₀) ∈ I and f′(a₀) is a unit modulo I, so the henselian property gives a root a of f with a ≡ a₀ modulo I. The value g(a) is a unit modulo I, hence a unit, because I lies in the Jacobson radical; this gives the map τ sending X to a.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/StandardEtaleLifting.lean`: the Lean file is the source byte for byte (SHA-256 `ba83e8107996c86c18afeb084a2c42854bd5cc7b5a9808f8f2ad341b9579e1ba`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
