# Integrated operators of test functions

Module `Langlands.Representation.Unitary.TestFunctionOperators` works on a second countable
locally compact Hausdorff group `G` with a left Haar measure `μ`. A *test function* is a
function `φ : G → ℂ` that is measurable, bounded and compactly supported (`IsTestFunction`, the
hypothesis shape of `Langlands.Analysis.TemperedIrreducibleComponentStatement`). For a jointly
continuous representation `ρ` on a complex Banach space (`IsContinuousRepresentation`), the
module constructs the integrated operator `ρ(φ) v = ∫ φ(g) • ρ(g) v dμ(g)` and proves the facts
about it used in the proof of that statement.

## Declarations

| Declaration | Content |
| --- | --- |
| `IsTestFunction`, `IsTestFunction.integrable`, `IsTestFunction.comp_mul_left` | test functions are integrable and stable under left translation |
| `continuous_orbit`, `exists_opNorm_le_of_isCompact` | orbits are continuous; `‖ρ(g)‖` is bounded on compact sets (Banach–Steinhaus) |
| `integrable_smul_orbit` | `g ↦ φ(g) • ρ(g) v` is Bochner integrable |
| `testOp μ ρ hρ φ hφ`, `testOp_apply` | the bounded operator `ρ(φ)`; its value is definitionally the Bochner integral |
| `norm_testOp_le`, `norm_testOp_sub_le` | for norm-preserving `ρ`: `‖ρ(φ)‖ ≤ ‖φ‖₁` and `‖ρ(φ₁) - ρ(φ₂)‖ ≤ ‖φ₁ - φ₂‖₁` |
| `comp_testOp` | `ρ(p) ρ(φ) = ρ(φ(p⁻¹ ·))` (left invariance of `μ`) |
| `intertwiner_comp_testOp` | an intertwiner `j` of two representations satisfies `j ρ(φ) = ρ'(φ) j` |
| `integral_smul_mem_of_continuous`, `testOp_mem` | Bochner integrals of continuous functions with values in a closed submodule stay in it; closed invariant submodules are `ρ(φ)`-invariant |
| `IsApproxIdentity`, `exists_approxIdentity`, `IsApproxIdentity.tendsto` | a sequence of nonnegative test functions of integral one with supports shrinking to `1` exists, and `ρ(χ_n) v → v` for every jointly continuous `ρ` |
| `tendsto_integral_norm_translate_sub` | left translation is continuous in `L¹(G)` |
| `continuous_comp_testOp` | for norm-preserving `ρ`, `g ↦ ρ(g) ρ(φ)` is continuous in operator norm |

## Proofs

The bound on compact sets is Mathlib's `banach_steinhaus` applied to the family `ρ(g)`, `g ∈ K`,
which is pointwise bounded because orbits are continuous. The approximate identity is
`χ_n = μ(U_n)⁻¹ 1_{U_n}` for `U_n` the interiors of `V_n ∩ K`, with `(V_n)` an antitone basis of
neighbourhoods of `1` (first countability) and `K` a compact neighbourhood of `1`; convergence
`ρ(χ_n) v → v` follows from `‖∫ χ_n(g) (ρ(g) v - v)‖ ≤ sup_{g ∈ U_n} ‖ρ(g) v - v‖`.
The `L¹` continuity of translation is Mathlib's continuity of the domain action of `Gᵈᵐᵃ` on
`Lp` (`Lp.instContinuousSMulDomMulAct`, for Haar measures of locally compact groups);
combined with `comp_testOp` and `norm_testOp_sub_le` it gives the operator-norm continuity of
`g ↦ ρ(g) ρ(φ)`.

## Provenance

Internal. These are standard facts about integrated representations (compare G. B. Folland,
*A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press 2015, registered as
`folland-2015-abstract-harmonic-analysis-second`, §3.2, printed pp.79–83); the module proves them
from Mathlib and does not transcribe a particular source.
