# Counting finite-field points of a separated algebraic space by degree strata

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

Let `c` be a `SepChart` (a separated algebraic space `X` with an affine étale surjective chart,
the symmetric tuple quotients `V_n` and the étale maps `e_n : V_n → X`; see
`SeparatedChart.md` and `DegreePoints.md`), `M` a scheme and `g : X → h_M` a morphism.

## Contents

- `eq_of_specMap_comp_eq`: two `κ`-points `z₁, z₂` of a separated algebraic space are equal
  once they agree after a field extension `κ → Ω`. The pullback of `z₂` along `z₁` is
  represented by a scheme `P`. Separatedness makes `P → Spec κ × Spec κ` a closed immersion
  (`closedImmersion_pair_of_isPullback`). The common `Ω`-point gives an `Ω`-point of `P` over
  the diagonal, so the diagonal `Spec κ → Spec κ × Spec κ` lifts to `P`
  (`exists_lift_of_isClosedImmersion`), which forces `z₁ = z₂`.
- `eq_of_map_toOverHom_eq`: the functor of points over `S0` is faithful on scheme morphisms.
- `p n : V_n → M` is the scheme morphism with `e_n ≫ g = h(p n)`, by full faithfulness of the
  Yoneda embedding. `ptE_g` says that the image in `M` of `ptE n v` is `v ≫ p n`.
- `fibrePoints g κ m` is the type of `κ`-points `z` of `X` (morphisms from the functor of
  points of `Spec κ`) with `z ≫ g = h(m)`. `degreePoints g κ m n` is the type of `κ`-points
  `v` of `V_n` with `v ≫ p n = m` whose point lies outside the threshold open
  `tupleSymmetricThresholdOpen n (n + 1)`.
- `degreeFibreEquiv`: for a finite field `κ` and `m : Spec κ → M`, the map
  `(n, v) ↦ ptE n v` from `Σ n < N, degreePoints g κ m n` to `fibrePoints g κ m` is a
  bijection. `Ω` denotes an algebraic closure of `κ`, which is Galois over `κ` because finite
  fields are perfect.
  - Injectivity (`degreeToFibre_injective`) holds for every field `κ`. After base change to `Ω`,
    `le_of_ptE_eq` in both directions gives equal degrees, and `eq_of_ptE_eq` gives equal
    `Ω`-points. Then `spec_hom_ext` gives equal `κ`-points, since `V_n` is affine.
  - Surjectivity (`degreeToFibre_surjective`): the `Ω`-point of `X` underlying `z` is
    `ptE n w` for some `n < N` and some `w` outside the threshold (`exists_ptE_eq`). By
    uniqueness (`eq_of_ptE_eq`), `w` is invariant under `Aut(Ω / κ)`, so it descends to a
    `κ`-point `v` of `V_n` (`exists_desc_of_aut_invariant`). Then `ptE n v = z` by
    `eq_of_specMap_comp_eq`, and `v ≫ p n = m` by `eq_of_map_toOverHom_eq`.
- `degreePointsEquiv`: the points in `degreePoints g κ m n` are the `κ`-points over `m` of the
  exact-degree scheme `D_n = tupleSymmetricDegreeScheme n`. `D_n` is the reduced closed
  subscheme of `V_n` on the complement of the threshold open, with closed immersion
  `tupleSymmetricDegreeι n`. A `κ`-point of `V_n` whose point lies outside the threshold
  factors through `D_n`, because `Spec κ` is reduced: by
  `Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`, the vanishing ideal
  of the closed set is contained in the kernel. The lift is `IsClosedImmersion.lift`.
- `card_fibrePoints`: when every `V_n` has finitely many `κ`-points, the number of `κ`-points
  of `X` over `m` is `∑_{n < N} #{d ∈ D_n(κ) | d ↦ m}`.
