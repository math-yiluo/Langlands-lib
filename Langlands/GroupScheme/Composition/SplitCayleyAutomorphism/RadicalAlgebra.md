# Stable subspaces and rigidity modulo the unit for Zorn's algebra

Coordinates on Zorn's algebra are `(a, u₁, u₂, u₃, v₁, v₂, v₃, b)`, indexed `0, …, 7`, as in
`RootGroups.md`. The unit is `unit = (1, 0, …, 0, 1)` and `Pi.single i 1` is the `i`-th standard
basis vector. This file holds the matrix algebra used for the triviality of the unipotent radical
of the split Cayley automorphism group. It proves two of the statements of `Interface.md` and
defines the action on the quotient of `A⁸` by the line of the unit.

## Expansion of root elements

- `quadCoeff α x` is the coefficient of `r²` in `x_α(r) x` (the root-group action `rootFun` of
  `RootGroups.md`). For a short root it is a single coordinate: for example
  `quadCoeff u₁ x = -x₄ · e₁` and `quadCoeff v₁ x = -x₁ · e₄`. For a long root it is `0`.
- `linCoeff α x = x_α(1) x - x - quadCoeff α x` is the coefficient of `r`.
- `rootFun_eq_expand`: `x_α(r) x = x + r · linCoeff α x + r² · quadCoeff α x` over every
  commutative ring. The proof checks it coordinate by coordinate for each of the twelve roots.

## Stable subspaces

- `coeff_mem_of_rootFun_mem`: let `W` be a subspace of `k⁸` over a field `k` containing `w` and
  all `x_α(r) w`. If `k` has an element `c` other than `0` and `1`, then `linCoeff α w` and
  `quadCoeff α w` lie in `W`. Write `X = linCoeff α w` and `Y = quadCoeff α w`. Taking `r = 1`
  and `r = c` puts `X + Y` and `cX + c²Y` in `W`. Then `(c - c²) Y` lies in `W`, and
  `c - c² = c(1 - c)` is nonzero.
- `single_one_mem_of_ne_zero`: if `a ≠ 0` and `a · eⱼ ∈ W` then `eⱼ ∈ W`.
- `stableSubspace : StableSubspaceStatement`. Let `k` be algebraically closed, hence infinite,
  so it has an element `c ∉ {0, 1}`. Let `W` be stable under all root elements and contain a
  vector `w` that is not a multiple of the unit. The proof shows `W` contains `e₁, …, e₆`. The
  torus hypothesis of the statement is not used.
  - Once `e₁ ∈ W`: the long-root coefficients `linCoeff l₂₁ e₁ = e₂` and `linCoeff l₃₁ e₁ = e₃`
    give `e₂, e₃`. The short-root coefficients `quadCoeff vᵢ eᵢ = -e_{i+3}` give `e₄, e₅, e₆`.
  - To get `e₁`, the proof splits into cases on the coordinates of `w`. The long-root
    coefficients `linCoeff l₁₂ e₂ = e₁` and `linCoeff l₁₃ e₃ = e₁` reduce `e₂` and `e₃` to `e₁`.
    - If `w₄ ≠ 0`, `w₅ ≠ 0` or `w₆ ≠ 0`, then `quadCoeff uᵢ w = -w_{i+3} eᵢ` gives `eᵢ`.
    - If instead `wᵢ ≠ 0` for some `i ∈ {1, 2, 3}`, then `quadCoeff vᵢ w` gives `e_{i+3}`, and
      `quadCoeff uᵢ e_{i+3} = -eᵢ` gives `eᵢ`.
    - Otherwise `w = (w₀, 0, …, 0, w₇)` with `w₀ ≠ w₇`, because `w` is not a multiple of the
      unit. Then `linCoeff u₁ w = (w₀ - w₇) e₁`.

## Rigidity modulo the unit

- `unitRigidity : UnitRigidityStatement`. Let `A` be a commutative ring and `g` an automorphism
  matrix with `g eᵢ = eᵢ + cᵢ · 1` for `i = 1, …, 6`. The Zorn products
  `e₁e₄ = e₂e₅ = e₃e₆ = e₀` give three expressions for `g e₀`:
  `(e₁ + c₁ 1)(e₄ + c₄ 1)`, `(e₂ + c₂ 1)(e₅ + c₅ 1)` and `(e₃ + c₃ 1)(e₆ + c₆ 1)`. Comparing
  the coordinates `1, 2, 4, 5` of the first two, and the coordinates `3, 6` of the first and
  the third, gives `c₁ = … = c₆ = 0`. Hence `g e₀ = e₀`, and `g e₇ = e₇` because `g` fixes the
  unit `e₀ + e₇`. So `g` fixes every basis vector and `g = 1`.

## The quotient by the line of the unit

- `projLin A : A⁸ → A⁷` is `x ↦ (x₁, …, x₆, x₇ - x₀)`. Its kernel is the line of the unit:
  `projLin_unit` shows the unit maps to `0`, and `eq_smul_unit_of_projLin_eq_zero` shows that
  `projLin x = 0` implies `x = x₀ · 1`.
- `sectLin A : A⁷ → A⁸` is `y ↦ (0, y₁, …, y₇)`, with `projLin_sectLin`
  (`projLin ∘ sectLin = id`) and `sectLin_projLin` (`sectLin (projLin x) = x - x₀ · 1`).
- `projMat A` and `sectMat A` are their matrices.
  `quotMatrix g = projMat A * g * sectMat A` is the `7 × 7` matrix induced by an `8 × 8`
  matrix `g`.
  - `quotMatrix_mulVec`: `quotMatrix g y = projLin (g (sectLin y))`.
  - `quotMatrix_mulVec_projLin`: if `g` fixes the unit then
    `quotMatrix g (projLin x) = projLin (g x)`.
  - `quotMatrix_mul`: if `g` fixes the unit then `quotMatrix (g h) = quotMatrix g · quotMatrix h`.
  - `quotMatrix_one`: `quotMatrix 1 = 1`.
  - `quotMatrix_eq_of_mulVec`: two `7 × 7` matrices with the same action on all vectors are equal.
- Compatibility with ring homomorphisms `f : A → B`:
  - `projLin_map`: applying `f` to the coordinates of `projLin x` gives `projLin` of `f x`.
  - `projMat_map` and `sectMat_map`: `f` sends `projMat A` and `sectMat A` to `projMat B` and
    `sectMat B`.
  - `quotMatrix_map`: `(quotMatrix g).map f = quotMatrix (g.map f)`.

## Provenance

The quotient representation and the stable-subspace argument are internal to this project. In
terms of the seven-dimensional quotient `k⁸ / k · 1`, `stableSubspace` says that every nonzero
subspace stable under the root groups contains the images of `u₁, …, v₃`. All statements are
proved directly in Zorn coordinates and are not quoted from the literature.
