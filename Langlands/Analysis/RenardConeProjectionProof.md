# Projection on a cone in a Euclidean space (Renard V.5.5): proof

Author: Worker 229.

Module `Langlands.Analysis.RenardConeProjectionProof`, namespace
`Langlands.Renard`.

## Result

`Langlands.Renard.coneProjectionStatements` proves the published proposition
`Langlands.Renard.ConeProjectionStatements` (module
`Langlands.Analysis.RenardConeProjectionStatements`, Renard 2026, V.5.5,
Proposition and Corollary, printed pp.127–128 / PDF pp.133–134). Its type is
exactly `ConeProjectionStatements.{u, v}`. It is the pair of
`coneProjectionStatement : ConeProjectionStatement.{v}` (the Proposition) and
`coneProjectionBasisStatement : ConeProjectionBasisStatement.{u, v}` (the
Corollary). The statement module and its Markdown are imported unchanged, and
no hypothesis is added. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Besides the statement module, the file imports
`Mathlib.Analysis.InnerProductSpace.Projection.Minimal` (projection on a
complete convex set), `Mathlib.Analysis.InnerProductSpace.Dual` (Riesz
representation `InnerProductSpace.toDual`) and
`Mathlib.Analysis.LocallyConvex.Separation` (geometric Hahn–Banach).

Renard proves existence through the projection theorem for closed convex sets
and leaves the equivalences (i) ⟺ (ii) ⟺ (iii) to the reader. For the
Corollary he expands `v₀` in the basis `ω` and `v₀ − v` in the basis `α`. The
Lean proof takes the same route and supplies the omitted details as below.

## General lemmas (namespace `Langlands.Renard.ConeProjection`)

Throughout, `E` is a real inner product space and `⟨ , ⟩` is `inner ℝ`.

- `nearest_iff_inner_le_zero`: for a convex `K` and `v₀ ∈ K`,
  `(∀ w ∈ K, ‖v − v₀‖ ≤ ‖v − w‖) ↔ ∀ w ∈ K, ⟨v − v₀, w − v₀⟩ ≤ 0`. Mathlib's
  `norm_eq_iInf_iff_real_inner_le_zero` gives the equivalence of the right side
  with `‖v − v₀‖ = ⨅ w : K, ‖v − w‖`. That equality is equivalent to the left
  side by `le_ciInf` and `ciInf_le`; the range is bounded below by `0`.
- `eq_of_inner_le_zero`: at most one point of `K` satisfies the obtuse-angle
  inequality. If `v₀, v₁ ∈ K` both do, then
  `⟨v₁ − v₀, v₁ − v₀⟩ = ⟨v − v₀, v₁ − v₀⟩ − ⟨v − v₁, v₁ − v₀⟩`. The first term
  is `≤ 0` (inequality at `v₀`, tested on `v₁`). The second is `≥ 0`
  (inequality at `v₁`, tested on `v₀`, after `v₀ − v₁ = −(v₁ − v₀)`). Hence
  `‖v₁ − v₀‖² ≤ 0` and `v₀ = v₁`.
- `exists_inner_le_zero`: in finite dimension, a nonempty closed convex `K`
  contains a point satisfying the obtuse-angle inequality. `E` is complete
  (`FiniteDimensional.complete`), so `exists_norm_eq_iInf_of_complete_convex`
  gives a point realizing the infimum distance. `norm_eq_iInf_iff_real_inner_le_zero`
  converts this.
- `inner_nonneg_of_mem_closure`: if `0 ≤ ⟨u, w⟩` for all `u ∈ A`, `w ∈ B`,
  the same holds for `u ∈ closure A`, `w ∈ closure B`. The set
  `{p : E × E | 0 ≤ ⟨p.1, p.2⟩}` is closed and contains `A ×ˢ B`, hence its
  closure, which is `closure A ×ˢ closure B` (`closure_prod_eq`).
- `tendsto_add_smul`: `x + ε • y → x` as `ε → 0⁺`, by continuity.
- `exists_pos_add_smul_mem`: if `C` is open and `a ∈ C`, then
  `a + ε • y ∈ C` for some `ε > 0` (from `tendsto_add_smul`).
- `inner_pos_of_inner_nonneg`: if `C` is open, `u ≠ 0` and `0 ≤ ⟨u, w⟩` on
  `C`, then `0 < ⟨u, w⟩` on `C`. For `w ∈ C`, pick `ε > 0` with
  `w − ε • u ∈ C`. Then `0 ≤ ⟨u, w⟩ − ε ⟨u, u⟩`, and `⟨u, u⟩ > 0`.

The remaining general lemmas assume that `C` is stable under multiplication by
positive reals (`hcone`).

- `zero_mem_closure`: if `C` is nonempty, then `0 ∈ closure C`, as the limit of
  `ε • x` (`x ∈ C`, `ε → 0⁺`).
- `smul_mem_closure`: if `C` is nonempty, then `closure C` is stable under
  multiplication by `t ≥ 0`. The case `t = 0` is `zero_mem_closure`. For
  `t > 0`, scaling is continuous and maps `C` into `C` (`map_mem_closure`).
- `exists_inner_pos`: in finite dimension, for a nonempty convex open cone
  `C ≠ E`, some `u` has `0 < ⟨u, w⟩` for all `w ∈ C`. Take `x ∉ C`.
  `geometric_hahn_banach_open_point` gives a continuous linear `f` with
  `f a < f x` for `a ∈ C`; let `z` be its Riesz representative, so
  `⟨z, y⟩ = f y`. Then `f ≤ 0` on `C`: if `f a > 0`, then with
  `t = |f x| / f a + 1 > 0` the point `t • a ∈ C` has
  `f (t • a) = |f x| + f a > f x`, a contradiction. Also `z ≠ 0`, since
  otherwise `f a < f x` reads `0 < 0`. So `−z` is nonzero with `0 ≤ ⟨−z, w⟩`
  on `C`, and `inner_pos_of_inner_nonneg` makes the pairings positive.
- `mem_closure_dual`: under the same hypotheses, every `u` with
  `0 ≤ ⟨u, w⟩` for all `w ∈ C` lies in the closure of
  `Č = {u | ∀ w ∈ C, 0 < ⟨u, w⟩}`. With `u₁` from `exists_inner_pos`,
  `u + ε • u₁ ∈ Č` for every `ε > 0`, and it tends to `u`.

## Lemmas on a basis and its dual family

Here `α : Module.Basis ι ℝ E` with `ι` finite, and `ω : ι → E` satisfies
`⟨αᵢ, ωⱼ⟩ = δᵢⱼ` (`hαω`). Write `K = {x | ∀ i, 0 ≤ ⟨αᵢ, x⟩}`.

- `eq_zero_of_inner_basis`: a vector orthogonal to every `αₖ` is zero. Expand
  it as `∑ (α.repr y i) • αᵢ` in its own inner product `⟨y, y⟩`.
- `inner_basis_sum`: `⟨αₖ, ∑ tᵢ ωᵢ⟩ = tₖ`.
- `eq_sum_dual`: `x = ∑ ⟨αᵢ, x⟩ ωᵢ`, since the difference is orthogonal to
  every `αₖ`.
- `eq_sum_basis`: `x = ∑ ⟨x, ωⱼ⟩ αⱼ`. Pairing `x = ∑ (α.repr x i) αᵢ` with
  `ωⱼ` shows that the `j`-th coordinate is `⟨x, ωⱼ⟩`.
- `sum_compl_eq`, `sum_mem_eq`: a sum over `Finset.univ \ F` (resp. over `F`)
  as a sum over all indices with coefficients set to `0` on `F` (resp. off
  `F`).
- `inner_basis_sum_compl`: `⟨αₖ, ∑_{i ∉ F} tᵢ ωᵢ⟩` is `0` if `k ∈ F` and `tₖ`
  otherwise.
- `closure_cone_eq`: `closure {∑ tᵢ ωᵢ | ∀ i, tᵢ > 0} = K`. The cone lies in
  `K` by `inner_basis_sum`, and `K` is closed as an intersection of closed
  half-spaces. Conversely, for `x ∈ K` and `ε > 0`,
  `x + ε • ∑ ωᵢ = ∑ (⟨αᵢ, x⟩ + ε) ωᵢ` (by `eq_sum_dual`) lies in the cone and
  tends to `x`.
- `convex_nonneg_cone`: `K` is convex.
- `decomposition_inner_le_zero`: if `v = ∑_{i ∉ F} tᵢ ωᵢ − ∑_{j ∈ F} sⱼ αⱼ`
  with `tᵢ > 0` (`i ∉ F`) and `sⱼ ≥ 0` (`j ∈ F`), then
  `p = ∑_{i ∉ F} tᵢ ωᵢ` lies in `K` and satisfies the obtuse-angle inequality
  on `K`. Membership follows from `inner_basis_sum_compl`. For `w ∈ K`,
  `v − p = −∑_{j ∈ F} sⱼ αⱼ`, so
  `⟨v − p, w − p⟩ = −∑_{j ∈ F} sⱼ ⟨αⱼ, w⟩ + ∑_{j ∈ F} sⱼ ⟨αⱼ, p⟩`. The second
  sum vanishes because `⟨αⱼ, p⟩ = 0` for `j ∈ F`. The first is `≥ 0` because
  `sⱼ ≥ 0` and `⟨αⱼ, w⟩ ≥ 0`.
- `mem_iff_inner_eq_zero`: with `tᵢ > 0` off `F`,
  `k ∈ F ↔ ⟨αₖ, ∑_{i ∉ F} tᵢ ωᵢ⟩ = 0`, by `inner_basis_sum_compl`.

## Proof of the Proposition (`coneProjectionStatement`)

Fix `E`, `C` (open, convex, nonempty, a cone) and `v`. `closure C` is convex
(`Convex.closure`), so `nearest_iff_inner_le_zero` gives (i) ⟺ (ii) for every
`v₀ ∈ closure C`.

- *Existence and uniqueness.* `exists_inner_le_zero` applied to the nonempty
  closed convex set `closure C` gives a point satisfying (ii), hence (i). If
  two points of `closure C` satisfy (i), both satisfy (ii), and
  `eq_of_inner_le_zero` makes them equal.
- *(i) ⟺ (iii) when `C ≠ E`.* Replace (i) by (ii).
  - (ii) ⟹ (iii). `0` and `2 • v₀` lie in `closure C` (`zero_mem_closure`,
    `smul_mem_closure`). Testing (ii) on them gives `⟨v − v₀, v₀⟩ ≥ 0` and
    `⟨v − v₀, v₀⟩ ≤ 0`, so `⟨v − v₀, v₀⟩ = 0`. Then for `w ∈ C`, (ii) reads
    `⟨v − v₀, w⟩ ≤ 0`, i.e. `0 ≤ ⟨v₀ − v, w⟩`. So `v₀ − v` lies in the closure
    of `Č` by `mem_closure_dual`.
  - (iii) ⟹ (ii). Every element of `Č` has positive pairings with `C`, so
    `inner_nonneg_of_mem_closure` gives `0 ≤ ⟨v₀ − v, w⟩` for
    `w ∈ closure C`. With `⟨v − v₀, v₀⟩ = 0`,
    `⟨v − v₀, w − v₀⟩ = −⟨v₀ − v, w⟩ ≤ 0`.

## Proof of the Corollary (`coneProjectionBasisStatement`)

Fix `ι`, `E`, `α`, `ω` with `⟨αᵢ, ωⱼ⟩ = δᵢⱼ`, and `v`, and let `C` be the open
cone `{∑ tᵢ ωᵢ | tᵢ > 0}`. By `closure_cone_eq`, `closure C = K`, which is
convex.

- *Second part (projection).* Given a decomposition with data `F`, `t`, `s`,
  `decomposition_inner_le_zero` shows that `∑_{i ∉ F} tᵢ ωᵢ` lies in `K` and
  satisfies the obtuse-angle inequality on `K`. `nearest_iff_inner_le_zero`
  turns this into the nearest-point property on `K = closure C`.
- *Existence of `F`.* `K` is closed (it equals `closure C`) and contains `0`.
  `exists_inner_le_zero` gives `v₀ ∈ K` with
  `⟨v − v₀, w − v₀⟩ ≤ 0` for all `w ∈ K`. Put `aᵢ = ⟨αᵢ, v₀⟩` and
  `bⱼ = ⟨v₀ − v, ωⱼ⟩`.
  - `aᵢ ≥ 0` because `v₀ ∈ K`.
  - `bⱼ ≥ 0`: `v₀ + ωⱼ ∈ K` (its `α`-pairings are `aᵢ + δᵢⱼ ≥ 0`), and testing
    the inequality on it gives `⟨v − v₀, ωⱼ⟩ ≤ 0`.
  - `⟨v₀ − v, v₀⟩ = 0`, by testing on `0` and `2 • v₀`, as in the Proposition.
  - Expanding `v₀ = ∑ aᵢ ωᵢ` (`eq_sum_dual`) gives
    `⟨v₀ − v, v₀⟩ = ∑ aᵢ bᵢ`. This is a sum of nonnegative terms equal to `0`,
    so `aᵢ bᵢ = 0` for every `i` (`Finset.sum_eq_zero_iff_of_nonneg`).

  Let `F = {i | aᵢ = 0}`. Then `aᵢ > 0` for `i ∉ F`, and
  `v₀ = ∑_{i ∉ F} aᵢ ωᵢ` because the dropped terms have `aᵢ = 0`. Also
  `v₀ − v = ∑ⱼ bⱼ αⱼ` (`eq_sum_basis`) and `bⱼ = 0` for `j ∉ F` (since
  `aⱼ ≠ 0` and `aⱼ bⱼ = 0`), so `v₀ − v = ∑_{j ∈ F} bⱼ αⱼ`. Hence
  `v = ∑_{i ∉ F} aᵢ ωᵢ − ∑_{j ∈ F} bⱼ αⱼ`, with `t = a` and `s = b`.
- *Uniqueness of `F`.* Let `G`, `t`, `s` be another decomposition. By
  `decomposition_inner_le_zero`, `∑_{i ∉ G} tᵢ ωᵢ` and `∑_{i ∉ F} aᵢ ωᵢ` both
  lie in `K` and satisfy the obtuse-angle inequality on `K`. So they are equal
  by `eq_of_inner_le_zero`. By `mem_iff_inner_eq_zero`, `k ∈ G` iff
  `⟨αₖ, ∑_{i ∉ G} tᵢ ωᵢ⟩ = 0`, iff `⟨αₖ, ∑_{i ∉ F} aᵢ ωᵢ⟩ = 0`, iff `k ∈ F`.
  So `G = F`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, literature id
`renard-2026-representations-groupes-reductifs-padiques`, V.5.5, Proposition
and Corollary, printed pp.127–128 / PDF pp.133–134. The Markdown of the
statement module quotes the passage and records the formal choices
(convexity, nonemptiness, and `C ≠ E` in (iii)).
