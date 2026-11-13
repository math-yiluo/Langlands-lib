# Root multiplicities of resultants along power-series branches

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`.

Provenance. In Schmidt, *Zur Methode von Stepanov* (Acta Arith. 24, 1973), the auxiliary
polynomial in one variable is a norm (a resultant in `Y`) of a bivariate polynomial `A`, and its
root multiplicity at `x` is bounded below by adding the vanishing orders of `A` along the points
of the curve above `x`. This module proves that lower bound for power-series roots of
`fh(x + T, Y)`; the argument (factor off the known roots and use multiplicativity of the
resultant) is our own formalisation route.

## Definitions

- `iota L x : F[X] →+* L⟦T⟧`, `p(X) ↦ p(x + T)`, for a field extension `L / F` and `x ∈ F`;
  `iota_C`, `iota_X`.

## Results

- `iota_eq`: `iota L x p` is the image in `L⟦T⟧` of the Taylor shift `taylor x p`;
  `iota_injective`.
- `le_rootMultiplicity_of_X_pow_dvd_iota`: for `p ≠ 0`, if `T^k ∣ iota L x p` then
  `k ≤ p.rootMultiplicity x` (via `rootMultiplicity_eq_natTrailingDegree` of the Taylor shift).
- `mul_card_le_rootMultiplicity_resultant`: let `fh, A ∈ F[X][Y]` with `fh ≠ 0`,
  `natDegree A ≤ D`, and `Res_Y(fh, A)` (Sylvester sizes `natDegree fh` and `D`) nonzero. Let
  `S ⊆ L⟦T⟧` be a finite set of roots of `fh(x + T, Y)` such that `T^M ∣ A(x + T, Φ)` for every
  `Φ ∈ S`. Then `M · #S ≤ rootMultiplicity x (Res_Y(fh, A))`.

  Proof: the monic polynomial `Q = ∏_{Φ ∈ S} (Y - Φ)` divides `fh(x + T, Y) = Q · R`. Mapping
  the resultant along `iota` (`resultant_map_map`), multiplicativity in the first argument
  (`resultant_mul_left`), `resultant_prod_left` and `resultant_X_sub_C_left` give
  `iota(Res(fh, A)) = (∏_{Φ ∈ S} A(x + T, Φ)) · Res(R, A(x + T, Y))`, which is divisible by
  `T^(M · #S)`. No splitting hypothesis is needed.
