# From scheme charts of the base to the algebraic-space estimate

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

## Contents

- `ringTestIso κ`: for any structure of `ULift ℤ`-algebra on a field `κ`, the test object
  `ringTest (ULift ℤ) κ` of ring points (`Spec κ` with the structure map of the algebra) is
  isomorphic to `toOver (Spec κ)`. The two have the same underlying scheme, and all
  morphisms to the terminal scheme `Spec (ULift ℤ)` agree.
- `ringPointsEquiv X κ`: the `κ`-points `RingPoints (ULift ℤ) X κ` of an algebraic space,
  which are sections of its presheaf over `ringTest (ULift ℤ) κ`, correspond to morphisms
  `h(toOver (Spec κ)) → X`. This is the Yoneda bijection `uliftYonedaEquiv`, composed with the
  isomorphism above. `ringPointsEquiv_map` gives naturality in morphisms of spaces
  (`uliftYonedaEquiv_symm_comp`).
- `card_ringPoints_fibre`: for `f : Y → B` and `x ∈ B(κ)`, the number of `y ∈ Y(κ)` with
  `RingPoints.map f y = x` equals the number of morphisms `y : h(Spec κ) → Y` with
  `y ≫ f = ringPointsEquiv B κ x`.
- `spaceUniformLangWeil_of_charts`: take `f : Y → B` with the hypotheses of
  `uniformLangWeil_fibreProduct`, and finitely many affine schemes `M i` locally of finite type
  over `ℤ` with morphisms `t i : h(M i) → B`. Suppose every point of `B` with values in a
  finite field is `h(m) ≫ t i` for some `i` and some `m : Spec κ → M i`. Assuming the two
  statements in families, the conclusion of `SpaceUniformLangWeilStatement` holds: there is
  `C > 0` with `|N_x − (#κ)^d| ≤ C (#κ)^(d − 1/2)` for every finite field `κ` (with any
  `ULift ℤ`-algebra structure) and every `x ∈ B(κ)`. `uniformLangWeil_fibreProduct` gives a
  constant `C_i` for each chart, and `C = 1 + ∑_i C_i` works for all of them. `x` corresponds
  to `h(m) ≫ t i` for some `i` and `m`, and `card_ringPoints_fibre` translates the count.
