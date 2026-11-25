# The Artin character at p of a rational principal idele

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalPrimeFactor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p`, `k ≥ 0` and `x : ℚˣ`, the file computes the factor at `p` among the finite-place Artin characters of the principal idele of `x` in the rational cyclotomic field of level `p ^ k`.

- `rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime`: `rationalCyclotomicPrincipalFinitePlaceCharacter p k x p`, the cyclotomic character in `(ZMod (p ^ k))ˣ` of the chosen finite-place Artin symbol at `p`, is the reduction modulo `p ^ k` of the unit `p ^ (−v_p(x)) · x` of `ℤ_[p]`.

For `k = 0` both sides lie in the trivial group `(ZMod 1)ˣ`. For `k = n + 1` the statement is `rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula`, which rests on the ramified Artin-symbol formula of `RationalCyclotomicFinitePlaceArtin`. The file only removes the restriction to positive exponents.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicPrincipalPrimeFactor.lean`: the Lean file is the source byte for byte (SHA-256 `13bdbc93773981af0036e6233ba70025b782dc29fabe46199dfb28da66719d1e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
