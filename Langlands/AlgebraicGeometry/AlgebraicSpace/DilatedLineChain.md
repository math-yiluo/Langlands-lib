# Countably many affine lines glued along the line with `p` inverted

Author: Worker 105.

Helper module for the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedOfSeparatedStatement`.
It contains no statement from the literature. It builds the scheme used as the
counterexample. The module works over any commutative ring `R` and any `p ∈ R`.

## Construction

For every `j : ℕ` take an affine line `Spec R[u_j]` (all are `Spec R[X]` in Lean). Glue them
along the common open `W = Spec L`, with `L = R[t][1/p]`, using `CommonOpenGluing`. The line
`j` contains `W` through `u_j = (t - p^j)/p^(j+1)`, that is `t = p^j + p^(j+1) u_j`. The index
type is `ULift ℕ`, to stay in universe `u`.

Informally, over a valuation ring `R = O` with `0 < ‖p‖ < 1`, the generic fibre is the affine
line with coordinate `t`. The `O`-points of the line `j` are the disc `|t - p^j| ≤ |p|^(j+1)`.
This module proves nothing about generic fibres or `O`-points.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.DilatedLineChain`, for `R` and `p`.

- `L = Localization.Away (C p : R[X])`; `P` and `T` are the images of `p` and `t = X` in `L`,
  and `e = IsLocalization.Away.invSelf (C p)` is the inverse of `P` (`P_mul_e`, `isUnit_P`).
  `algebraMap_R_L` computes the algebra map `R → L` through `R[X]`.
- `σ j : R[X] →+* L`, `X ↦ (T - P^j) e^(j+1)` (the coordinate `u_j` on `W`), and
  `τ j : R[X] →+* L`, `X ↦ P^j + P^(j+1) T`. The lemmas `σ_C`, `τ_C`, `σ_X`, `τ_X` give their
  values on constants and on `X`.
- `σ' j`, `τ' j : L →+* L`: the maps induced by `σ j` and `τ j`
  (`IsLocalization.Away.lift`, since both send `p` to the unit `P`). `σ'_algebraMap`,
  `τ'_algebraMap` and `σ'_comp` record that they extend `σ j` and `τ j`; `σ'_P`, `τ'_P`,
  `τ'_e` and `pow_P_mul_e` are the computation rules used next.
- `σ'_τ'` and `τ'_σ'`: `σ' j` and `τ' j` are inverse. The proofs check the generators with
  `IsLocalization.ringHom_ext` and `Polynomial.ringHom_ext`, using `(P e)^(j+1) = 1`.
  `σEquiv j : L ≃+* L` packages them.
- `g j = Spec.map (σ j) : Spec L ⟶ Spec R[X]` for `j : ULift ℕ`. `g_eq` writes it as
  `Spec.map (σ' j) ≫ Spec.map (algebraMap R[X] L)`: an isomorphism followed by the inclusion
  of the basic open `D(p)`. Hence `g j` is an open immersion (instance).
- `glued` (the glued scheme) and `ι j` (the line open immersions), from `CommonOpenGluing`.
- `σ_comp_algebraMap`, `g_comp_structure`: all lines have the same structure morphism to
  `Spec R` on the common open.
- `toBase : glued ⟶ Spec R` (`CommonOpenGluing.desc`) and `ι_toBase`: on each line it is the
  structure morphism `Spec R[X] ⟶ Spec R`.
