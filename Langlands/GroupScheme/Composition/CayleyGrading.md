# Gradings of a Cayley datum and the rank bound

This module defines gradings of a `CayleyDatum K` (module
`Langlands.GroupScheme.Composition.CayleyDatum`) by an additive abelian
group, and proves that a grading whose degrees generate a lattice `ℤ^I`
forces `|I| ≤ 2`. It works over every field `K`, in every characteristic.
It uses the identities of
`Langlands.GroupScheme.Composition.CayleyIdentities` (`form` is the polar
form `b` of the norm `N`, `trace x` is `T(x) = b(x, 1)`).

## Definitions

- `Grading M` (for `[AddCommGroup M] [DecidableEq M]`) presents a grading
  of the algebra by its projection matrices. It has a family
  `proj : M → Matrix (Fin 8) (Fin 8) K` and a finite set `support`, with
  these conditions:
  - `mem_support`: `m ∈ support` exactly when `proj m ≠ 0`.
  - `sum_proj`: the projections in the support sum to `1`.
  - `proj_mul_proj`: `proj m * proj n` is `proj m` if `m = n` and `0`
    otherwise.
  - `proj_unit`: the unit is homogeneous of degree `0`.
  - `proj_mul`: if `x` has degree `a` and `y` has degree `b`, then `xy`
    has degree `a + b`.

  "`x` has degree `m`" means `proj m *ᵥ x = x`.

## Results

- `unit_ne_zero`: the unit of a Cayley datum is nonzero (since `N(1) = 1`).
- Elementary facts about a grading `g`: `proj_mulVec_of_eq`, `proj_proj`,
  `proj_eq_zero`, `eq_zero_of_not_mem` (a homogeneous vector whose degree
  is outside the support is zero), `sum_proj_mulVec`,
  `mul_eq_zero_of_not_mem`, `proj_unit_of_ne`.
- `trace_eq_zero`: a homogeneous vector `x` of nonzero degree `a` has
  `T(x) = 0`. Proof: `x² = T(x) x - N(x) 1` has degree `2a ≠ a`, so
  applying `proj a` gives `T(x) x = 0`. If `x = 0` then `T(x) = 0` anyway.
- `form_eq_zero`: homogeneous vectors of degrees `a`, `b` with `a + b ≠ 0`
  are orthogonal for `b`. This uses `T(xy) = T(x) T(y) - b(x, y)`, where
  `T(xy) = 0` and one of `T(x)`, `T(y)` is zero.
- `exists_form_eq_one`: a nonzero vector `x` of degree `a` pairs to `1`
  with some vector of degree `-a`. By nondegeneracy, some `w` has
  `b(x, w) ≠ 0`. By `form_eq_zero`, only the degree `-a` component of `w`
  contributes, and we rescale it.
- `exists_ne_zero`: every degree in the support has a nonzero homogeneous
  vector (a column of the nonzero projection).
- `neg_mem_support`: the support is symmetric. `zero_mem_support`: `0` is
  in the support.
- `card_support_le`: the support has at most eight elements. Nonzero
  homogeneous vectors of distinct degrees are linearly independent.
- `add_mem_or_sub_mem`: if `a, b` are in the support, then `b + a` or
  `b - a` is in the support. Take `x` of degree `a`, `y` of degree `-a`
  with `b(x, y) = 1`, and `z ≠ 0` of degree `b`. If neither degree occurs,
  then `xz = 0` and `yz = 0`. The linearized identity (I4L)
  `(T(x) yz - x(yz)) + (T(y) xz - y(xz)) = b(x, y) z` then gives `z = 0`.
- `coeff_eq_zero_of_not_mem_span`: over `ℚ`, if `x ≠ 0`,
  `y ∉ span{x}` and `z ∉ span{x, y}`, then `rx + sy + tz = 0` forces
  `r = s = t = 0`.
- **`Grading.card_le_two`**: if `g : c.Grading (I → ℤ)` (with `I` a
  finite type) has
  `AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤`, then
  `Fintype.card I ≤ 2`.

## Proof of `Grading.card_le_two`

Let `ρ : ℤ^I → ℚ^I` be the coordinatewise cast. We claim that the images
of all degrees lie in the `ℚ`-span of two vectors. Otherwise, pick `a` in
the support with `ρ a ≠ 0`, `b` with `ρ b ∉ span{ρ a}`, and `d` with
`ρ d ∉ span{ρ a, ρ b}`. Then `p ↦ p₀ a + p₁ b + p₂ d` is injective on
`ℤ³`. By `add_mem_or_sub_mem` there is `σ = ±1` with `σa + b` in the
support. The nine pairwise distinct degrees
`0, ±a, ±b, ±d, ±(σa + b)` are then all in the support, by symmetry and
`zero_mem_support`. This contradicts `card_support_le`.

Since the degrees generate `ℤ^I`, every standard basis vector maps into
that two-dimensional span. So the span is all of `ℚ^I`, and
`|I| = dim ℚ^I ≤ 2`. The rank is computed over `ℚ` rather than `ℤ`,
because the `ℤ`-span version of the claim fails in the presence of
torsion.

## Provenance

This is internal, derived content written for this development. The
fact that the weights of a split torus acting on a Cayley algebra
span a lattice of rank at most two reflects the rank of `G₂` (Knus,
Merkurjev, Rost and Tignol, *The Book of Involutions*, Section 33.C and
Theorem 25.14, as cited in the target statement's Markdown). The
combinatorial argument above does not use any classification. It uses
only the composition identities, through `trace_eq_zero`, `form_eq_zero`
and `add_mem_or_sub_mem`, together with `dim = 8`.
