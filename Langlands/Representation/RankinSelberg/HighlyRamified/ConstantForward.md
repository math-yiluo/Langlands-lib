# A monomial gamma factor and a monomial dual integral give a constant forward integral

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: from (14) and (15) to (13), printed pages 329–330).

- `spectralPoint_one_sub`: `q^(-(1-s)) = q⁻¹ (q^(-s))⁻¹`.
- `forward_eq_const_of_monomial`: suppose the forward integral `I` and the dual integral `J`
  have rational continuations `R` and `R_d`, and they satisfy the published pointwise
  `GammaFunctionalEquation` with the gamma factor `rationalEpsilonMonomial C N`
  (that is, `C X^N`). If `J(s) = c_d X^(-N)` on a right half-plane, then on a right half-plane
  `I(s) = (ζ^e)⁻¹ C⁻¹ c_d q^N`. Proof: uniqueness of rational continuations
  (`HasRationalContinuation.unique`) identifies `R_d` with `c_d X^(-N)`, and the functional
  equation at `s` reads `c_d q^N X^N = ζ^e C X^N R(X)`.

In the application, `N = (m+2)(m+1)a(χ)` is the exponent supplied by the monomial gamma input,
and the dual integral is a monomial of degree `-N` because the Kirillov vector is supported on
the shell `ϖ^(-c) GL(O)` with `c = (m+2) a(χ)`.
