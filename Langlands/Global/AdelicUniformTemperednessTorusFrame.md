# Simple-root and central coordinates on the positive maximal split torus

Module `Langlands.Global.AdelicUniformTemperednessTorusFrame`, namespace
`Langlands.Global.StandardParabolicFamily`.

Let `𝓕` be a standard parabolic family (`StandardParabolicFamily F G`) of a connected reductive
group `G` over a number field `F`, with maximal split torus `T` and simple relative roots `Δ`.
The normalized logarithm `characterLog` identifies the positive real points
`A_T = intrinsicSubgroup F 𝓕.T` with the real character dual `𝔞_T = RealCharacterDual F T`.

## Definitions

- `TorusFrame 𝓕` (structure): linear coordinates `e : 𝔞_T ≃L[ℝ] (Δ → ℝ) × (Fin r → ℝ)` with
  positive scales `step α`. The `α`-th root coordinate is `ℓ(α) / step α`
  (`root`). The central coordinates vanish exactly when the restriction of `ℓ` to the rational
  characters of `G` vanishes (`central`).
- `TorusFrame.crd Fr x = Fr.e (characterLog x)`: the coordinates of a point `x` of `T(𝔸)`.

## Results

- `TorusFrame.nonempty`: a frame exists. It is built from the group data of
  `exists_isLocalFinitenessGroupData` and the coordinates of `localFinitenessTorusCoordinates`.
- `eq_of_characterLog_eq'`, `exists_characterLog_eq'`: on `A_T` the logarithm is injective and
  onto `𝔞_T`. `characterValue_eq_one_of_characterLog_eq_zero`: a character with logarithm `0` at
  a positive point takes the value `1` there.
- `map_i_injective`: `T(𝔸) → G(𝔸)` is injective.
- `map_p_positivePointMap`, `exists_splitPoint`, `normCharacter_splitPoint`: a positive point of
  `T` on which the simple roots in `J` take the value `1` is the image of a positive point of the
  split component `A_J`, and the two points have the same image in `G(𝔸)`. For every character
  `χ` of `T`, the idele norm of `𝓕.f J ≫ χ` at the point of `A_J` equals that of `χ` at its
  image in `T`. This uses `positiveTorusSplitComponent`.
- `TorusFrame.crd_mul`, `crd_pow`, `characterLog_root` (`log |α(x)| = step α · crd x α`),
  `exists_crd_eq` (every coordinate vector is attained on `A_T`), `eq_of_crd_eq`.
- `TorusFrame.exists_split`: a positive point `x` is a product `x₁ x₀ x_c` of positive points.
  At `α ∈ J` their root coordinates are `0`, `0` and that of `x`. At `α ∉ J` they are the
  positive part, the negative part and `0`. The central coordinates of `x₀` and `x_c` vanish.
- `TorusFrame.exists_pow_eq`: `N`-th roots in `A_T` with coordinates divided by `N`.
- `TorusFrame.characterValue_eq_one`: a simple root with vanishing coordinate at a positive point
  takes the value `1` there.

## Source

The coordinates are the standard ones on `𝔞_0 = 𝔞_G ⊕ 𝔞_0^G` (Mœglin–Waldspurger 1995, I.1.4).
They are used here for the estimates of the uniform temperedness criterion (MW Lemma I.4.1;
Delorme 2023, Proposition 3.6).
