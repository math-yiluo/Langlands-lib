# Bivariate Taylor expansion and filtered ring homomorphisms

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`; not a result of the
literature. It plays the role of the Taylor expansions with hyperderivatives `E^{(i,j)}` in
Schmidt, *Zur Methode von Stepanov* (Acta Arith. 24, 1973), Section 3, but is set up as a ring
homomorphism so that it works in every characteristic without division by factorials.

## Contents

- `instCommRingPolyPoly`: a shortcut instance `CommRing (Polynomial (Polynomial R))`. Without it,
  instance search fails on the four-fold nested polynomial ring `F[X][Y][U][V]`. It is equal to
  the instance found by `inferInstance`.
- `map_fil_of_inBox`: a ring homomorphism `φ : F[X][Y] →+* A` sends the box `(a, b)` of
  `Box.lean` into any monotone, additive, multiplicative filtration `Fil a b` on `A` that
  contains `φ (C (C r))` in degree `(0, 0)`, `φ (C X)` in degree `(1, 0)` and `φ Y` in
  degree `(0, 1)`. Proof: expand `P` into monomials `r X^i Y^j`.
- `InBox2 a b Ψ` for `Ψ ∈ F[X][Y][U][V]` (outer variable `V`): the coefficient of `U^e₀ V^e₁`
  lies in the box `(a - e₀, b - e₁)`; with `inBox2_zero`, `InBox2.add`, `InBox2.mono`,
  `InBox2.mul`, `inBox2_C_C`, `inBox2_X`, `inBox2_C_X`.
- `thetaX : F[X] →+* F[X][Y][U]`, `p(X) ↦ p(X + U)`, and
  `theta : F[X][Y] →+* F[X][Y][U][V]`, `P(X, Y) ↦ P(X + U, Y + V)`, both via
  `Polynomial.eval₂RingHom`; simp lemmas `theta_C_C`, `theta_C_X`, `theta_X`.
- `inBox2_theta`: if `P` lies in the box `(a, b)` then `theta P` satisfies `InBox2 a b`
  (application of `map_fil_of_inBox` with `Fil = InBox2`).
- `theta_map_evalZero`: setting `U = 0` in `theta P` gives `taylor X (P.map C)`, the Taylor
  expansion in `Y` alone.
- `theta_coeff_zero`: the coefficient of `U^0 V^k` of `theta P` is the Hasse derivative
  `hasseDeriv k P` (in `Y`); in particular `theta_coeff_zero_zero` (it is `P` for `k = 0`) and
  `theta_coeff_one_zero` (it is `derivative P`, the `Y`-derivative, for `k = 1`).
