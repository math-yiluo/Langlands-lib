# The exponential of a real Banach algebra as a local diffeomorphism

`Langlands.Geometry.Manifold.LinearLieGroup.Exponential`. For a complete normed real algebra `𝔸`
(not necessarily finite-dimensional), the exponential `NormedSpace.exp : 𝔸 → 𝔸` near `0`, in the
form used for the charts of linear Lie groups. Namespace `Langlands.LinearLieGroup`.

## Content

- `contDiff_exp 𝔸`: `exp` is smooth of every order (it is analytic).
- `exp_add_of_commute'`: `exp (x + y) = exp x * exp y` for commuting `x`, `y`. Mathlib's
  `NormedSpace.exp_add_of_commute` is stated for normed `ℚ`-algebras, a structure that a normed
  real algebra does not receive as an instance; this version goes through
  `exp_add_of_commute_of_mem_ball` over `ℝ`.
- `expPartialHomeomorph 𝔸 : OpenPartialHomeomorph 𝔸 𝔸`: the derivative of `exp` at `0` is the
  identity (`hasStrictFDerivAt_exp_zero_equiv`), so the inverse function theorem gives a local
  inverse; it is restricted to the open set `expRegularSet 𝔸` where the derivative of `exp` is
  invertible. Its coercion is `exp` (`coe_expPartialHomeomorph`), `0` is in its source, `1` in its
  target, and its inverse, a local logarithm, sends `1` to `0`.
- `contDiffOn_expPartialHomeomorph_symm`: the local logarithm is smooth on the whole target, by the
  inverse function theorem at each point of the source, where the derivative is invertible.
- `expUnit 𝔸 X : 𝔸ˣ`: `exp X` with inverse `exp (-X)`; it is continuous.

The charts of `IsExpLieAlgebra` (`Basic`) and the exponential charts of `𝔸ˣ` (`Units`) are built
from these.

## Literature

The exponential of a Banach algebra and its local inverse near `1`: B. C. Hall, *Lie groups, Lie
algebras, and representations*, 2nd edition (Springer GTM 222, 2015), chapter 2, §2.3, Theorem 2.8,
p. 38 (`log A = ∑ (-1)^{m+1} (A - I)^m / m` for `‖A - I‖ < 1`, with `e^{log A} = A`, and
`log e^X = X` for `‖X‖ < log 2`), and §2.4, Proposition 2.16, p. 42 (`exp` is smooth); the proof
here is the inverse function theorem of Mathlib. Hall treats `n × n` complex matrices and defines
the logarithm by its power series; here `𝔸` is any complete normed real algebra.

## Source and licence

Port of `src/GroundTheory/AutomorphicForms/RealGroupsLie.lean`, lines 10–90 (section `ExpChart`),
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Namespace `GroundTheory.Automorphic` becomes `Langlands.LinearLieGroup`.
- The source works over a field `𝕂` with `[RCLike 𝕂]` and `[NormedAlgebra 𝕂 𝔸]`; here the field is
  `ℝ` and no longer an argument: `expPartialHomeomorph 𝕂 𝔸` becomes `expPartialHomeomorph 𝔸`,
  `expUnit 𝕂 𝔸` becomes `expUnit 𝔸`, `contDiff_exp 𝕂 𝔸` becomes `contDiff_exp 𝔸`, and likewise for
  the lemmas of the section; the `include 𝕂 in` lines are removed.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration are added.
- Statements and proofs are otherwise unchanged.
