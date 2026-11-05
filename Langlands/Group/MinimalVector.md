# Minimal vectors and star-stable stabilizers

Author: Worker 1359.

This module proves an elementary minimal-vector lemma for matrix groups over
an arbitrary `RCLike` field `𝕜`, so for both the real and the complex numbers.
It is one step of a planned route to a self-adjoint matrix realization of a
reductive group. It does not prove that realization.

## Setting

Fix finite index types `n` and `m` and a group homomorphism
`π : GL n 𝕜 →* GL m 𝕜`. No continuity, algebraicity or other property of `π`
is assumed, except in the main theorems. They also assume that `π` is
compatible with conjugate transpose:

    hπ : ∀ g, π (star g) = star (π g).

Here `star` on a matrix unit is its conjugate transpose. Over the real
numbers it is the transpose.

- `act π g` is the continuous linear operator on `EuclideanSpace 𝕜 m` given
  by the matrix of `π g`. It is defined through Mathlib's star-algebra
  equivalence `Matrix.toEuclideanCLM`, which sends conjugate transpose to the
  Hilbert-space adjoint for the standard inner product. `act_mul` and
  `act_one` say that this is an action.
- `stabilizer π w` is the subgroup of all `g` with `act π g w = w`.
- `IsMinimalVector π w` means `‖w‖ ≤ ‖act π g w‖` for every `g`. So `w` has
  the smallest Euclidean norm in its orbit.

## Results

- `inner_apply_eq_of_isSelfAdjoint`: a self-adjoint continuous operator
  satisfies `⟪R x, y⟫ = ⟪x, R y⟫`.
- `sq_apply_eq_of_norm_le`: let `R` be a self-adjoint operator on a complete
  inner product space. If `‖w‖ ≤ ‖R w‖` and `‖R (R w)‖ ≤ ‖w‖`, then
  `R (R w) = w`.
- `act_star` and `isSelfAdjoint_act`: under `hπ`, `act π (star g)` is the
  adjoint of `act π g`. If the matrix of `p` is positive definite, then
  `act π p` is self-adjoint.
- `inner_act_star_mul`: under `hπ`,
  `⟪act π (star g * g) x, y⟫ = ⟪act π g x, act π g y⟫`.
- `star_mem_stabilizer` (main lemma): under `hπ`, if `w` is a minimal vector
  and `g` stabilizes `w`, then `star g` stabilizes `w`. So the stabilizer of
  a minimal vector is stable under conjugate transpose.
- `mem_stabilizer_act_iff`: `g` stabilizes `act π x w` if and only if
  `x⁻¹ * g * x` stabilizes `w`.
- `exists_isMinimalVector_of_isClosed`: if the orbit
  `Set.range fun g => act π g w` is closed in `EuclideanSpace 𝕜 m`, then
  `act π x w` is a minimal vector for some `x`.
- `exists_conj_star_mem_stabilizer`: under `hπ`, if the orbit of `w` is
  closed, there is an `x` such that, for every `g`, if `x⁻¹ * g * x` is in
  `stabilizer π w` then so is `x⁻¹ * star g * x`. In other words, the
  conjugate subgroup `{g | x⁻¹ * g * x ∈ stabilizer π w}` (the stabilizer of
  `act π x w`) is stable under conjugate transpose.

## Proof

For `sq_apply_eq_of_norm_le`, self-adjointness gives
`⟪R (R w), w⟫ = ⟪R w, R w⟫ = ‖R w‖²`. Expanding the norm of a difference,

    ‖R (R w) - w‖² = ‖R (R w)‖² - 2 ‖R w‖² + ‖w‖² ≤ ‖w‖² - 2 ‖w‖² + ‖w‖² = 0,

so `R (R w) = w`.

For `star_mem_stabilizer`, let `h = star g * g`. Its matrix is
`gᴴ * g` with `g` invertible, so it is positive definite. Let
`s = positivePower h hh (1/2)` and `r = positivePower h hh (1/4)`, the spectral
powers from the published module `Langlands.Group.AlgebraicPolar`. They are
positive definite, `r * r = s` by `positivePower_add`, and `s * s = h` by
`positivePower_half_sq`. Hence `act π s` and `act π r` are self-adjoint.
Since `act π g w = w`,

    ‖act π s w‖² = re ⟪act π s (act π s w), w⟫ = re ⟪act π h w, w⟫
                 = re ⟪act π g w, act π g w⟫ = ‖w‖².

Apply `sq_apply_eq_of_norm_le` to `R = act π r`. Minimality gives
`‖w‖ ≤ ‖act π r w‖`, and `‖act π r (act π r w)‖ = ‖act π s w‖ = ‖w‖`. So
`act π s w = w`, hence `act π h w = w`. Finally,
`act π h w = act π (star g) (act π g w) = act π (star g) w`.

For `exists_isMinimalVector_of_isClosed`, Euclidean space is proper. Mathlib's
`IsClosed.exists_infDist_eq_dist`, applied to the nonempty closed orbit and
the origin, gives an orbit point `act π x w` nearest to the origin. Every
`act π g (act π x w) = act π (g * x) w` is in the orbit, so its distance to
the origin is at least that of `act π x w`. The last theorem combines this
with `mem_stabilizer_act_iff` and the main lemma.

## Provenance and scope

The statements and proofs are internal; no literature statement is used. The
idea of minimizing the norm on an orbit is that of Kempf and Ness, but this
module neither quotes nor depends on their paper.

Intended use: let `G` be a reductive subgroup of `GL n ℂ`. Suppose there is a
representation `π` compatible with conjugate transpose and a vector `w` with
closed orbit whose stabilizer is the point group of `G`. Then a conjugate of
`G` is stable under conjugate transpose. Such `π` and `w` would come from
Matsushima's closed-orbit criterion, which is not proved here. That criterion,
its algebraic inputs (invariant theory and complete reducibility), the real
case and the passage to actual group schemes are all remaining obligations of
`Langlands.GroupScheme.ConnectedReductiveSelfAdjointRealizationStatement`.
