# The linear system over an affine noetherian base

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `exists_framed_cover`: a quasi-compact scheme carries a finite ordered affine cover with frames
  of a given line bundle on its members.
- `nonempty_rep`: a representing scheme of the Grassmannian of rank-one quotients exists (Library
  `Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`).
- `exists_model` (`R` noetherian, `π : X ⟶ Spec R` proper, flat, geometrically integral, `L` a line
  bundle): there are a Čech representative `C` of `L`, a representing scheme `D` of the Grassmannian
  of rank-one quotients of `C.Q` and an ideal sheaf `W` on `X ×_R D.Gr` such that
  `LinearSystemGluing.IsUniversalOn π [L] ⊤ D.p W` holds: `W` is in the linear system of `[L]`
  (relative effective Cartier with `[O(W)] = [L] + [N]`), and over every locally noetherian test
  every divisor of the linear system is the pullback of `W` along exactly one point.
- `exists_affine_universal`: the same packaged with `D.Gr` locally noetherian and `D.p` proper.

## Source

Kleiman, *The Picard scheme*, Theorem 3.13 and Exercise 3.14 (pp.25–26), over an affine noetherian
base, with `P(Q)` realized as the Library's representing scheme of the Grassmannian of rank-one
quotients of `Q`.
