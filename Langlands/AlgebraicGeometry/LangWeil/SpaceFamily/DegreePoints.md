# Field points of a separated algebraic space and its symmetric tuple charts

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

Let `c` be a `SepChart` (`SeparatedChart.lean`): a separated algebraic space `X` with an affine
étale surjective chart `a : U → X`, the étale equivalence relation `R ⇉ U`, the schemes `W_n` of
distinct related `(n + 1)`-tuples, their symmetric quotients `V_n` and the étale maps
`e_n : V_n → X`. The Library's threshold open `tupleThresholdOpen k ⊆ U` is the saturation under
`R` of the set of first coordinates of distinct related tuples of length `k + 1` (points of
`W_k`). `tupleSymmetricThresholdOpen n (n + 1) ⊆ V_n` is the open set of classes of tuples whose
first coordinate lies in `tupleThresholdOpen (n + 1)` (`tupleSymmetricMap_mem_threshold_iff`).

## Contents

- `homOver f` regards a morphism `T → Y.left` as a morphism `toOver T → Y` over `S0`.
- `ptA o` and `ptE n v` are the images in `X` of a point `o : T → U` of the chart and of a point
  `v : T → V_n`, as morphisms from the functor of points of `T`. `ptA_comp` and `ptE_comp` give
  naturality in `T`. `ptE_symmetricMap` says that the image of a tuple's class is the image of
  its first coordinate. `ptA_projection` says that all coordinates of a related tuple have the
  same image.
- `exists_rel_of_ptA_eq` and `ptA_eq_of_rel`: two points of the chart have the same image in
  `X` exactly when they are joined by a point of `R`, by the pullback property of the kernel
  pair.
- `injective_coordinates`: the coordinates of a distinct tuple with values in a field are
  pairwise different (the open of distinct tuples avoids the diagonals).
- `exists_coordinate_eq`: take a distinct tuple `a` of length `n + 1` and a distinct tuple `b` of
  length `k + 1`, both with values in an algebraically closed field `Ω`, with the same image in
  `X`. If the first coordinate of `a` lies outside `tupleThresholdOpen (n + 1)`, then every
  coordinate of `b` is a coordinate of `a` (Library `tupleField_coordinates_exhaust`).
- `le_of_ptE_eq`: if `w : Spec Ω → V_n` lies outside the threshold open and
  `v : Spec Ω → V_k` has the same image in `X`, then `k ≤ n`. Lift `w` and `v` to tuples
  along the surjective quotient maps (`exists_lift_of_surjective`). The coordinates of the lift
  of `v` inject into those of the lift of `w`.
- `eq_of_ptE_eq`: for `k = n`, the two points are equal: after lifting to tuples, every
  coordinate of the second tuple is a coordinate of the first, and the Library's
  `tupleSymmetricMap_eq_of_coordinate_matching` identifies their classes in `V_n`.
- `exists_tuple_of_mem_threshold`: an `Ω`-point `o` of `U` whose point lies in
  `tupleThresholdOpen k` is the first coordinate of a distinct related `Ω`-tuple of length
  `k + 1`. By definition of the threshold, the point of `o` is related through a point `r` of
  `R` to the first coordinate of a point of `W_k`. `exists_lift_at_point`, applied to the
  étale (hence locally quasi-finite) maps `t : R → U` and `W_k → U`, lifts these to an
  `Ω`-point `ρ` of `R` with `ρ ≫ t = o` and an `Ω`-tuple `a'` whose first coordinate is
  `ρ ≫ s`. All coordinates of `a'` have the image of `o` in `X`. If `o` is a coordinate of
  `a'`, a transposition moves it to the front (`tupleDistinctReindex`). Otherwise, replacing
  the first coordinate of `a'` by `o` gives an injective related family of `Ω`-points, which
  is a distinct tuple (`tupleDistinctFieldLift`).
- `exists_ptE_eq` (existence): every point `z` of `X` with values in an algebraically closed
  field is `ptE n v` for some `n < N` and some `v` outside the threshold open. `z` lifts to the
  chart (`exists_lift_atlas_algClosed`). The point of the lift lies in exactly one degree
  locus (`exists_unique_tupleDegreeLocus`), of some degree `n`. `v` is the class of a tuple of
  length `n + 1` starting with the lift.
