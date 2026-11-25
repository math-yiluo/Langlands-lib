# The closed-subgroup theorem for linear groups

`Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroup`. For a complete normed real algebra `𝔸`:
the Lie–Trotter product formula, the Lie algebra of a subgroup of `𝔸ˣ`, and von Neumann's theorem
that every closed subgroup of `𝔸ˣ` (for finite-dimensional `𝔸`) is a Lie group with exponential
charts. Namespace `Langlands.LinearLieGroup`; the steps of the proofs are in
`Langlands.LinearLieGroup.ClosedSubgroup`.

## Statements

- `tendsto_exp_mul_exp_pow X Y`: `(exp (n⁻¹ X) exp (n⁻¹ Y))^n → exp (X + Y)` as `n → ∞`. The difference
  `F(t) = exp (tX) exp (tY) - exp (t(X+Y))` has derivative `0` at `0`, so `n F(1/n) → 0`; and
  `‖aⁿ - bⁿ‖ ≤ n qⁿ ‖a - b‖ ‖1‖` when left multiplication by `a` and `b` is bounded by `q ≥ 1`, with
  `q = e^{(‖X‖+‖Y‖)/n}`.
- `lieAlgebra G = {X | ∀ t : ℝ, expUnit 𝔸 (t • X) ∈ G}`.
- `IsExpLieAlgebra.coe_eq_lieAlgebra`: if `IsExpLieAlgebra G 𝔤`, then `(𝔤 : Set 𝔸) = lieAlgebra G`.
  If `exp (tX) ∈ G` for all `t`, then for small `t ≠ 0` the vector `tX` lies in the neighbourhood of
  the field `exists_nhds`, hence in `𝔤`, hence `X ∈ 𝔤`.
- `lieSubmodule G hG`, for `hG : IsClosed (G : Set 𝔸ˣ)`: the subspace with underlying set
  `lieAlgebra G` (`coe_lieSubmodule` is `rfl`; `mem_lieSubmodule`). It is built as the subspace
  `ClosedSubgroup.lieSub S` of the closed multiplicative set `S`, the closure in `𝔸` of the image of
  `G`; a unit lies in `S` only if it lies in `G` (`coe_mem_closureImage_iff`), and `S` is closed
  under addition of exponents by the Lie–Trotter formula.
- `isExpLieAlgebra_of_isClosed G hG : IsExpLieAlgebra G (lieSubmodule G hG)` for finite-dimensional
  `𝔸`.

## von Neumann's argument

Let `L` be the Lie algebra of `S` and `W` a complement. Near `0`, the only `y ∈ W` with `exp y ∈ S` is
`0` (`ClosedSubgroup.eventually_eq_zero`): otherwise there are `yₙ → 0` in `W ∖ {0}` with
`exp yₙ ∈ S`; a subsequence of `yₙ / ‖yₙ‖` converges to a unit vector `u ∈ W`, and `exp (tu) ∈ S` for
all `t` because `tu` is the limit of the multiples `⌊t / ‖yₙ‖⌋ yₙ`
(`ClosedSubgroup.exp_smul_mem_of_tendsto`), so `u ∈ L ∩ W = 0`, a contradiction. The map
`z ↦ exp (p z) exp (z - p z)`, `p` the projection onto `L`, is a local diffeomorphism at `0`
(`ClosedSubgroup.map_exp_mul_exp`). So every `g ∈ S` near `1` is `exp (p z) exp (z - p z)` with
`exp (z - p z) = exp (-p z) g ∈ S` and `z - p z ∈ W` small, hence `z - p z = 0` and `g = exp (p z)`
with `p z ∈ L` (`ClosedSubgroup.eventually_exists_exp`). For `S` the closure of the image of `G`
this gives the field `exists_nhds` of `IsExpLieAlgebra`, with the local injectivity of `exp`.

With `IsExpLieAlgebra.isClosed` (`Basic`), a subgroup of `𝔸ˣ` carries the structure for some `𝔤`
exactly when it is closed, and then `𝔤 = lieAlgebra G`.

## Literature

The closed-subgroup theorem for matrix groups: B. C. Hall, *Lie groups, Lie algebras, and
representations*, chapter on the matrix exponential and the closed subgroup theorem; the Lie product
formula in the same chapter (page references to be added).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`:

| Source (under `src/`) | Lines | Content here |
|---|---|---|
| `Formalism/HermitianCurvature/HermitianCurvatureProofs/GroupGeneratedByExp.lean` | 17–122 | `ClosedSubgroup.norm_pow_mul_le` … `ClosedSubgroup.trotter` |
| `Development/AbelianVarietyTheory/Proofs/FlagMeasures/ClosedMatrixSubgroupTheorem.lean` | 19–132 | `ClosedSubgroup.pow_mem_of_mul` … `ClosedSubgroup.eventually_exists_exp` |
| `CompanionTheory/AutomorphicTheory/PadicUnitaryWeights/DixmierMalliavin/DixmierMalliavinFactorisationHolds.lean` | 14–35 | the proof of `isExpLieAlgebra_of_isClosed` (source: `CompanionTheory.DM.exists_lie`) |

The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespaces `Formalism.FourierDecayAlt.P.GroupGeneratedByExp` and `GlobalTheory.ClosedMatGroup`
  become `Langlands.LinearLieGroup.ClosedSubgroup`; the algebra is `{𝔸 : Type*}` (source:
  `{𝔸 : Type}`).
- `trotter` is also stated publicly as `tendsto_exp_mul_exp_pow`.
- New: `lieAlgebra`, `IsExpLieAlgebra.coe_eq_lieAlgebra`, `closureImage`, `coe_mem_closureImage_iff`,
  `lieSubmodule` (the source's `lieSub` of the closure of the image of `G`, with its carrier replaced
  by `lieAlgebra G` through `Submodule.copy`), `coe_lieSubmodule`, `mem_lieSubmodule`.
- `exists_lie` (`∃ 𝔤, IsExpLieAlgebra H 𝔤`) becomes `isExpLieAlgebra_of_isClosed` with the explicit
  `𝔤 = lieSubmodule G hG`; its proof is the source proof, with the final membership read through
  `lieSubmodule`'s carrier.
- The exponential lemmas lose their field argument (see `Exponential`); `push_neg` is written
  `push Not` (deprecation); unused section instances are left out with `omit … in`; in a tactic
  proof `letI` is written `let`.
- `import` lines are replaced by `Langlands.Geometry.Manifold.LinearLieGroup.Basic` and the Mathlib
  modules used.
- A module docstring and a docstring for every declaration are added.
