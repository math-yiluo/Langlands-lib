# Termination of the smoothening sequence: homogeneous forms in generators of the augmentation ideal

Author: Worker 348. Internal helper module for the final step of Kaletha–Prasad, Theorem A.6.2.
A member of the smoothening sequence with torsion-free cotangent module is smooth. This module
supplies the commutative algebra for that step. The argument is internal to this project.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `C` is an `R`-algebra with an `R`-point `ε` and augmentation ideal `I = augIdeal ε`.
`x : Fin d → C` are elements of `I` (`hx`). Polynomials are `MvPolynomial (Fin d) R`, and
`aeval x` evaluates them at `x`. `ϖ C` denotes the ideal `Ideal.span {algebraMap R C ϖ}`.

## Without independence

- `prod_pow_mem_pow` and `aeval_mem_pow`: a homogeneous polynomial of degree `j` takes values in
  `I ^ j` at `x`.
- `aeval_mem_span_of_dvd`: a polynomial whose coefficients are all divisible by `ϖ` takes values in
  `ϖ C`.
- `exists_isHomogeneous` (**spanning**): assume `hspan`, that every `y ∈ I` is `∑ r_i x_i`
  modulo `I²`. Then every element of `I ^ j` is `aeval x P` modulo `I ^ (j+1)` for a homogeneous
  `P` of degree `j`. The proof is by induction on `j`, using `I^(j+1) = I^j · I` and
  `Submodule.mul_induction_on`. The base case is `y - ε(y) ∈ I`.

## With graded independence

From here `R` is a domain. Assume `hspan` and `hind`: if `Q` is homogeneous of degree `n` and
`aeval x Q ∈ I ^ (n+1)`, then `Q = 0`.

- `mem_pow_of_smul_mem` (**saturation**): for `ϖ ≠ 0`, `ϖ c ∈ I ^ j` implies `c ∈ I ^ j`. By
  induction on `j`: write `c = P(x) + (I^(j+1))`; then `(C ϖ · P)(x) ∈ I^(j+1)`, so `C ϖ · P = 0`
  and `P = 0`.
- `dvd_coeff_of_mem_sup`: if `Q` is homogeneous of degree `n` and `aeval x Q ∈ I^(n+1) + ϖ C`,
  then `ϖ` divides every coefficient of `Q`. Write `Q(x) = i + ϖ c`. Then `ϖ c ∈ I^n`, so
  `c ∈ I^n` by saturation, so `c = P(x)` modulo `I^(n+1)` with `P` homogeneous. Graded
  independence gives `Q = ϖ P`.
- `mem_sup_of_sq_mem` (**square-zero elements**): for a prime `ϖ`, if `c² ∈ ϖ C`, then
  `c ∈ I^j + ϖ C` for every `j`. By induction on `j`: write `c = a + b` with `a ∈ I^j` and
  `b ∈ ϖ C`, and `a = P(x)` modulo `I^(j+1)`. Then `P²(x) ∈ I^(2j+1) + ϖ C`, so `ϖ` divides the
  coefficients of `P²`. In the polynomial ring over the domain `R ⧸ (ϖ)` the reduction of `P`
  squares to zero, so it is zero. Hence `ϖ` divides the coefficients of `P`, and
  `c ∈ I^(j+1) + ϖ C`.
