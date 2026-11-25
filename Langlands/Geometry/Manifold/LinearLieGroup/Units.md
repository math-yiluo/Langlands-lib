# The unit group as a linear Lie group

`Langlands.Geometry.Manifold.LinearLieGroup.Units`. For a complete normed real algebra `𝔸`, the
unit group `𝔸ˣ` with its exponential charts. Namespace `Langlands.LinearLieGroup`.

## Content

- `expChartUnits g : OpenPartialHomeomorph 𝔸ˣ 𝔸` is the exponential chart at `g`:
  `x ↦ log (g⁻¹ x)` for `g⁻¹ x` in the target of `expPartialHomeomorph 𝔸`, with inverse
  `X ↦ g · exp X`. It contains `g` in its source and sends it to `0`.
- `expChartUnits_mem_maximalAtlas`: every exponential chart belongs to the maximal atlas of
  Mathlib's manifold structure on `𝔸ˣ` (`Mathlib/Geometry/Manifold/Instances/UnitsOfNormedAlgebra`),
  whose only chart is the inclusion `Units.val`. Both transition maps are smooth:
  `X ↦ g · exp X` and `a ↦ log (g⁻¹ a)`.
- `isExpLieAlgebra_top`: `IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸)`; the neighbourhood
  of `0` is the whole source of `expPartialHomeomorph 𝔸`.

With finite-dimensional `𝔸`, this covers `GL_n(ℝ)`, `GL_n(ℂ)`, `GL_n` of a product of copies of `ℝ`
and `ℂ`, and the units of every finite-dimensional real algebra.

## Comparison with Mathlib's manifold structure

- `contMDiff_units_of_contDiff_val`: a map `p` from a normed space into `𝔸ˣ` is smooth for Mathlib's
  charted space when `x ↦ (p x : 𝔸)` is smooth (the inclusion is the only chart, and `Units.val` is
  an open embedding).
- `contMDiff_units_iff_top` (finite-dimensional `𝔸`): `f : 𝔸ˣ → F` is smooth for Mathlib's charted
  space on `𝔸ˣ` if and only if `x ↦ f x` on `⊤ : Subgroup 𝔸ˣ` is smooth for the exponential charted
  space `isExpLieAlgebra_top.chartedSpace`. By `IsExpLieAlgebra.contMDiff_iff_expG` the right side
  says that `Y ↦ f (g exp Y)` is smooth on `⊤ : Submodule ℝ 𝔸` for every `g`. For the left side,
  smoothness at `g` may be tested in the exponential chart `expChartUnits g`, which lies in the
  maximal atlas (`contMDiffWithinAt_iff_source_of_mem_maximalAtlas`); in that chart `f` reads
  `X ↦ f (g exp X)`. The two exponential maps differ only by the identification of `⊤` with `𝔸`.

So on `𝔸ˣ` the two smooth structures have the same smooth functions; the exponential charted space
is never an instance, and statements about `𝔸ˣ` in the Library use Mathlib's.

## Literature

B. C. Hall, *Lie groups, Lie algebras, and representations*, 2nd edition (Springer GTM 222, 2015),
chapter 2, §2.3, Theorem 2.8, p. 38 (the matrix logarithm as local inverse of `exp`), and chapter 3,
§3.8, Corollary 3.45, p. 70, whose proof (p. 71) uses the charts `A = A₀ e^X`, `‖X‖ < ε`. Hall
works in `GL(n; ℂ)` and its closed subgroups; here `𝔸` is any complete normed real algebra.

## Source and licence

The exponential charts and `isExpLieAlgebra_top` are ported from the repository
`leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`:

- `src/GroundTheory/AutomorphicForms/RealGroupsLie.lean`, lines 92–168 (section `UnitsChart`);
- `src/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean`, lines 301–305
  (`isExpLieAlgebra_top`).

The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.LinearLieGroup`.
- The field `𝕂` of the source is specialized to `ℝ` and is no longer an argument
  (`expChartUnits 𝕂 g` becomes `expChartUnits g`).
- `isExpLieAlgebra_top` is stated without the hypothesis `[FiniteDimensional ℝ 𝔸]`, which its proof
  does not use.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
- `contMDiff_units_of_contDiff_val` and `contMDiff_units_iff_top` are not in the source; they are
  written for the Library.
