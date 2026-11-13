# Duality intertwines P with I: proof

`Langlands.Algebra.dualityInduction` proves exactly the published proposition
`Langlands.Algebra.DualityInductionStatement`, with independent universe
parameters `uA`, `uB`, and `v`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, I.4.2, Theorem,
printed pp.23–24 / PDF pp.29–30. The implementation follows the direct evaluation
proof under the common complex coefficient hypothesis of the published statement.
Worker 261 implements this specialization of Worker 264's common
`NonUnitalTensorDuality` construction.

Apply `NonUnitalTensorDuality.naturalIso` with `S = B`, `R = A`, and `X = B`,
using the original left regular B-action and the supplied right A-action.
On each nondegenerate left A-module M, its component sends an element ψ of
`Hom_(A.op)(B, D_A(M))_B` to the functional
`b ⊗ m ↦ ψ(b)(m)` on `B ⊗_A M`. The inverse takes a functional λ to
`b ↦ (m ↦ λ(b ⊗ m))`. The helper proves these maps land in the actual
nondegenerate parts, intertwine the original right B-actions, are inverse, and
are natural in M.

The statement supplies nondegeneracy of the right A-action.
`NondegenerateTensorFunctor.regular_isNondegenerate` supplies nondegeneracy of
the left regular B-action using B's local idempotents.
`RenardRegularCoefficientAdapters.pInputCompatible` obtains the common
coefficient comparison from `IsScalarTower ℂ Aᵐᵒᵖ B`: the complex structure
recovered from the right A-action agrees with B's supplied complex structure,
which is compatible with its left multiplication.

The helper's Hom and tensor functors specialize definitionally to `rightI` and
`regularP`. Thus its natural isomorphism has exactly the required type
`I_AB(M̃) ≅ P_AB(M)^∼`. The proof adds no hypothesis, identifies no universes,
and needs no finite dimensionality or multiplicative identity.
