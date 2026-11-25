# Parameter congruences for Lubin–Tate polynomials

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with valuation ring `O` and residue field of cardinality `q`. The polynomial `f_π(X) = X^q + πX`, its iterates and the primitive polynomials `Q_n` depend polynomially on the parameter `π ∈ O`. The file records that two parameters with the same image under a ring map `O → R` give the same images of all these polynomials, and the corresponding statement modulo an ideal.

## Main results

Let `R` be a commutative ring (in any universe) and `f : O → R` a ring homomorphism; `π`, `ϖ` are arbitrary elements of `O`.

- `standardLubinTatePolynomial_map_eq_of_parameter_eq`, `standardLubinTatePolynomialIterate_map_eq_of_parameter_eq`, `standardLubinTatePrimitivePolynomial_map_eq_of_parameter_eq`: if `f(π) = f(ϖ)`, the images under `f` of `f_π` and `f_ϖ`, of their `n`-fold iterates, and of their primitive polynomials `Q_n` coincide.
- `standardLubinTatePrimitivePolynomial_eval₂_eq_of_parameter_eq`: under the same hypothesis, `Q_n` for `π` and for `ϖ` take the same value at every `x ∈ R` (coefficients mapped by `f`).
- `standardLubinTatePrimitivePolynomial_eval₂_sub_mem_of_parameter_sub_mem`: if `f(π) − f(ϖ) ∈ I` for an ideal `I` of `R`, then the two values of `Q_n` at any `x ∈ R` are congruent modulo `I`.

## Proof

Induction on the number of iterates for the equality statements; the congruence statement is the equality statement applied after composing with `R → R/I`.

## Points to watch

- The parameters need not be uniformizers, and nothing is assumed about the levels attached to them; the results are purely algebraic and independent of the characteristic.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`: the Lean file is the source byte for byte (SHA-256 `e8cc8570e37d4620aa23ef7ca10a92c40fe8c32d948ee21a3e4168760805251b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
