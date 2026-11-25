/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection

/-! # Section normalization of the boundary pullback tensor comparison

Source: Stacks Project, Tag 01CD.
(blueprint: lem-sc-boundary-pullback-tensor-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- The tensor comparison induced by uniqueness of left adjoints preserves unit sections.
Source: Stacks Project, Tag 01CD, pullback of tensor products; Tag 0096, adjunction.
(blueprint: lem-sc-boundary-pullback-tensor-unit).
Proof: Write boundaryPullbackComparison as the unique comparison with Mathlib pullback.
The unit-leftAdjointUniq equation identifies the chosen tensor-pullback unit followed
by the comparison with the Mathlib pullback unit. The monoidal pullback tensorator
sends that unit on a pure tensor to the tensor of the two unit sections: this follows
from its construction by the bilinear map on sections and the sheafification unit.
Expand boundaryPullbackTensorIso, apply these three unit comparison equations, and
cancel the inverse comparison on each factor. This proves the equality on each open
without any invertibility, closed immersion or square-zero assumption. The formula
also holds on the empty open and for zero modules by the same linear identities. -/
theorem boundaryPullbackTensorIso_unit_tmul {X Z : Scheme.{u}} (j : Z ⟶ X)
    (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app (M ⊗ N)).app U
          (tmulSection s t)) =
      tmulSection (M := (tensorPullback j).obj M) (N := (tensorPullback j).obj N)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M).app U s)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app N).app U t) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  have hunit (A : X.Modules) (a : Γ(A, U)) :
      ((boundaryPullbackComparison j).app A).hom.app (j ⁻¹ᵁ U)
        ((adj.unit.app A).app U a) = pullbackUnitApp j A U a := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app adj
      (pullbackPushforwardAdjunction j) A
    exact congrArg (fun φ ↦ φ.app U a) h
  have hinv (A : X.Modules) (a : Γ(A, U)) :
      ((boundaryPullbackComparison j).app A).inv.app (j ⁻¹ᵁ U)
        (pullbackUnitApp j A U a) = (adj.unit.app A).app U a := by
    rw [← hunit A a]
    exact congrArg (fun φ ↦ φ.app (j ⁻¹ᵁ U) ((adj.unit.app A).app U a))
      ((boundaryPullbackComparison j).app A).hom_inv_id
  change (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
    ((adj.unit.app (M ⊗ N)).app U (tmulSection s t)) = _
  simp only [boundaryPullbackTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rw [hunit (M ⊗ N) (tmulSection s t)]
  change (((boundaryPullbackComparison j).app M).inv ⊗ₘ
    ((boundaryPullbackComparison j).app N).inv).app (j ⁻¹ᵁ U)
      ((Functor.OplaxMonoidal.δ (pullback j) M N).app (j ⁻¹ᵁ U)
        (pullbackUnitApp j (M ⊗ N) U (tmulSection s t))) = _
  rw [pullback_δ_app_unit_tmulSection, tensorHom_app_tmulSection, hinv M s, hinv N t]

end
end AlgebraicGeometry.Scheme.Modules
