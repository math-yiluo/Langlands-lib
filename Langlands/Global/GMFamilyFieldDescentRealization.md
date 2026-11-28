# The field-descent formula for linear-algebra descent data

For descent data `D : FieldDescentData V₁ V`
([GMFamilyFieldDescentMetric](../LinearAlgebra/GMFamilyFieldDescentMetric.md)) with `V₁`
finite-dimensional, this module works in the coordinates
`E = EuclideanSpace ℝ (Fin (finrank ℝ V₁))` given by `D.e₁`. The fine roots are
`D.R = restrictRoots D.φ D.R₀` and the coarse subspace is `D.b`, the image of `B`. The main
theorem `FieldDescentData.hasFieldDescentFormula` proves `HasFieldDescentFormula D.R D.b`
([GMFamilyFieldDescent](GMFamilyFieldDescent.md)) by checking the hypotheses of
`hasFieldDescentFormula_of_restrictRoots` ([GMFamilyFieldDescentTransport](GMFamilyFieldDescentTransport.md)).

## Contents

- `inner_res_rv` and `res_rv`: the restriction of the vector of a root `γ` is the Riesz vector of
  `γ ∘ κ` in the coordinates `e₁`; `mem_R` describes the fine roots.
- `e₁_mem_centralSpace`: the central space of `D.R` is the image of `Z₁`.
- `isLeviSpace`: the image of `φ` is a Levi flat of `D.R₀`. A point of `V₁` on which no root
  `γ` with `γ ∘ κ ≠ 0` vanishes exists (`Module.Dual.exists_forall_ne_zero_of_forall_exists`), and
  `range_eq` identifies the flat it defines with the image of `κ`.
- `starProjection_mem_b`: the orthogonal projection to the central space preserves `D.b`, by
  `inner_F_central`.
- `inner_e₁_B_K`, `mem_b_of_orthogonal`: the images of `B` and `K` are orthogonal, and a vector
  orthogonal to the image of `K` lies in `D.b`. `restrictedRoot_b_eq_iff` compares restrictions to
  `D.b` through inner products with `B`.
- `m₀`, `m₀_rv`, `m₀_pos`: the multiplicities transported to the Euclidean roots.
- `special_sums`: the weighted sums of the fine roots over each nonzero restriction to `D.b` lie
  in `D.b`. Their inner product with the image of `y ∈ K` regroups as the sum of
  `mult γ · γ(κ y)` over a fibre of restriction to `B`, which vanishes by `special`.
