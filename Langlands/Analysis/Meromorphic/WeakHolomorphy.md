# Weakly holomorphic operator families on a finite-dimensional complex space

Module `Langlands.Analysis.Meromorphic.WeakHolomorphy` (namespace
`Langlands.Analysis.Meromorphic.WeakHolomorphy`) is a helper for the proof of
Bernstein–Lapid's Fredholm criterion
(`Langlands.Analysis.Meromorphic.FredholmCriterionProof`).

Setting: `E` is a complex normed space, finite-dimensional from
`exists_lipschitzAt_of_weak` on. `B` and `C` are complex normed spaces, with `B`
complete. `T ⊆ E` is open and `g : E → B →L[ℂ] C` is weakly holomorphic on `T`:
`z ↦ φ (g z v)` is complex differentiable on `T` for every `v : B` and every
continuous linear form `φ` on `C`. This is the chart form of
`IsHolomorphicOperatorFamilyOn` from
`Langlands.Analysis.Meromorphic.AnalyticSystems`.

## Results

- `exists_bound_of_weak`: if all `z ↦ φ (g z v)` are continuous on a compact
  set `K`, then `‖g z‖` is bounded on `K`. The uniform boundedness principle
  (`banach_steinhaus`) is applied twice. First it is applied to the vectors
  `g z v ∈ C`, viewed in the double dual
  (`NormedSpace.inclusionInDoubleDual`, an isometry), which gives
  `sup_z ‖g z v‖ < ∞` for each `v`. Then it is applied to the operators `g z`,
  using that `B` is complete.
- `exists_lipschitzAt_of_weak`: for `z₁ ∈ T` there are `r > 0` and `L` with
  `‖g z - g z₁‖ ≤ L ‖z - z₁‖` for `z` in the ball of radius `r` about `z₁`.
  Choose `R > 0` with closed ball `closedBall z₁ R ⊆ T`, and a bound
  `‖g z‖ ≤ M` there. For fixed `v` and `φ`, `h z = φ (g z v)` is
  differentiable on the ball and maps it into a closed ball of radius
  `2 M ‖v‖ ‖φ‖` about `h z₁`. The Schwarz lemma
  (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) gives
  `‖h z - h z₁‖ ≤ (2 M ‖v‖ ‖φ‖ / R) ‖z - z₁‖`. Taking the supremum over `φ`
  (`NormedSpace.norm_le_dual_bound`) and over `v` (`opNorm_le_bound`) gives the
  estimate with `L = 2M/R`.
- `isBigO_sub_of_weak`: the same estimate in the form
  `g z - g z₁ = O(z - z₁)` as `z → z₁`.
- `continuousAt_of_weak`: `g` is continuous in operator norm at every point of
  `T`.
- `differentiableOn_inverse_apply`: if `X : E → B →L[ℂ] B` is weakly
  holomorphic on `T` and every `X z`, `z ∈ T`, is invertible, then
  `z ↦ φ (Ring.inverse (X z) w)` is complex differentiable on `T` for all `w`
  and `φ`. So the family of inverses is again weakly holomorphic.
  `Ring.inverse` is Mathlib's total inverse, equal to `(X z)⁻¹` on units.
  Fix `z₁ ∈ T` and write `Y z = Ring.inverse (X z)`, `y₁ = Y z₁ w` and
  `ψ = φ ∘ Y z₁`. The resolvent identity `Y z - Y z₁ = Y z₁ (X z₁ - X z) Y z`
  gives, for `z ∈ T`,

  `φ (Y z w) = φ y₁ - (ψ (X z y₁) - ψ (X z₁ y₁)) - r z`,
  `r z = ψ ((X z - X z₁) (Y z w - y₁))`.

  The middle term is differentiable at `z₁` by weak holomorphy of `X`. For the
  remainder, `‖r z‖ ≤ ‖ψ‖ ‖X z - X z₁‖ ‖Y z w - y₁‖`. Here
  `X z - X z₁ = O(z - z₁)` by `isBigO_sub_of_weak`. Also `Y z w → y₁`, by
  continuity of `Ring.inverse` at units (`NormedRing.inverse_continuousAt`)
  composed with `continuousAt_of_weak`. Hence `r z = o(z - z₁)`, so `r` has
  derivative `0` at `z₁`, and `z ↦ φ (Y z w)` is differentiable at `z₁`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §3.2, p.193 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; arXiv TeX lines
654–664), note without proof that, by the uniform boundedness principle, an
analytic family of operators on a barrelled space, such as a Banach space, is
analytic in the strong (operator-norm) sense. They cite Grothendieck and
Bourbaki for this. In the proof of the Lemma in §3.4 (p.194) they use
that `s ↦ X_s⁻¹` is holomorphic. The arguments above are internal proofs of
exactly the consequences needed: local norm Lipschitz bounds and weak
holomorphy of the inverse family. They use Banach–Steinhaus and the Schwarz
lemma, and never construct an operator-valued derivative.
