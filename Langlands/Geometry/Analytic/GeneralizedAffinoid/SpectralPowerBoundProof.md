# Spectral bounds give radius-weighted power bounds in affinoid quotients

Author: Worker 1010.

Closing theorem: Worker 972.

The theorem `spectralPowerBound` has the type
`SpectralPowerBoundStatement K` for every normed field `K` that is
ultrametric and complete. Let `P` be a presentation with arbitrary positive
radii, `a : P`, and `r > 0` with `x a ≤ r` at every point `x` of the
spectrum. Then `a` has radius-`r` bounded powers: some `C > 0` gives
`‖a ^ n‖ ≤ C * r ^ n` for every `n`. No hypothesis on the valuation, on the
radii, on reducedness, or on the ideal is added.

## Reduction to the strict theorem

The shared `PresentedStrictAffinoidAlgebra.quotient_norm_one_le` from
[AffinoidUnitNorm](../AffinoidUnitNorm.md) shows that the quotient norm of
`1` in a strict presentation is at most one, because the quotient map does not
increase norms and the strict Tate algebra has `‖1‖ = 1`.

`hasRadiusBoundedPowers_of_strict_comparison` takes the following inputs:

- a presentation `P` over `K`, an element `a : P`, a radius `r > 0`, and the
  spectral hypothesis `x a ≤ r` for every point `x` of the spectrum of `P`;
- a complete ultrametric field `L` and an element `c : L` with `‖c‖ = r`;
- a strict presentation `Q` over `L`;
- a ring map `ψ : P →+* Q` with `‖ψ x‖ ≤ ‖x‖` and, for some `C > 0`,
  `‖x‖ ≤ C ‖ψ x‖`.

The proof sets `b = c⁻¹ ψ(a)` in `Q`, writing `c⁻¹` for its image under the
scalar map. Let `y` be a point of the spectrum of `Q`.

- Its pullback along the contractive map `ψ` is a point of the spectrum of
  `P`, so `y (ψ a) ≤ r`.
- `y` is bounded by the norm, and scalars satisfy `‖c⁻¹‖ ≤ r⁻¹` in `Q`. Hence
  `y (c⁻¹) ≤ r⁻¹`.

Therefore `y b ≤ 1`. The published theorem
`PresentedStrictAffinoidAlgebra.hasBoundedPowers_of_spectrum_le_one` gives a
`D > 0` with `‖b ^ n‖ ≤ D`. Since `ψ (a ^ n) = c^n b^n`, the lower bound for
`ψ` gives `‖a ^ n‖ ≤ C D r^n`.

## The closing theorem

`spectralPowerBound` combines three modules.

1. `RadiusRealization.nonempty` realizes the `P.arity + 1` positive radii
   `Fin.cons r P.polyradius` in one complete ultrametric field `L` over `K`.
   The realization supplies an isometric embedding `ι : K →+* L`, elements
   `R.c 0` of norm `r` and `R.c (i + 1)` of norm `P.polyradius i`, and a
   bounded `K`-linear retraction `π : L →+ K` with `π 1 = 1`.
2. `exists_strictBaseChange` from `GeneralizedAffinoid.StrictBaseChange`,
   applied to `ι`, `π` and the elements `R.c (i + 1)`, gives a strict
   presentation `Q` over `L` and a ring map `ψ : P →+* Q`. It satisfies
   `‖ψ x‖ ≤ ‖x‖` and `‖x‖ ≤ C * ‖ψ x‖` for some `C > 0`.
3. `hasRadiusBoundedPowers_of_strict_comparison`, applied with the element
   `R.c 0` of norm `r`, gives `HasRadiusBoundedPowers r a`.

The edge cases need no separate treatment. If `K` is trivially valued,
`RadiusRealization` still supplies `L`. If `P` has no variables, the family
of radii is just `r`. Zero quotients and nilpotent elements are handled by
the strict theorem.

