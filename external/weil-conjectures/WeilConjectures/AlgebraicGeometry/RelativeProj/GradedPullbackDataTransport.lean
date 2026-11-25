/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedBaseChangeTransport

/-! # Transport of graded-algebra pullback data

## References

* Stacks Project, Constructions, Tag 01O3
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.GradedAlgebraData

/-- The ring equivalence induced by one affine component of a graded-algebra isomorphism. -/
def gradedAlgebraSectionRingEquiv {X : Scheme.{u}} {A B : X.GradedAlgebraData}
    (e : A ≅ B) (U : X.affineOpens) : A.obj U ≃+* B.obj U where
  toFun := e.hom.app U
  invFun := e.inv.app U
  left_inv x := by
    have h := congrArg (fun f : A ⟶ A ↦ f.app U x) e.hom_inv_id
    exact h
  right_inv x := by
    have h := congrArg (fun f : B ⟶ B ↦ f.app U x) e.inv_hom_id
    exact h
  map_mul' := map_mul (e.hom.app U)
  map_add' := map_add (e.hom.app U)

/-- Transport the source and target graded algebras of coefficientwise pullback data.
The component map is the old one conjugated by the supplied graded-algebra isomorphisms;
coefficientwise base change and both restriction laws transport along them. -/
noncomputable def PullbackData.transport
    {X Y : Scheme.{u}} {g : Y ⟶ X}
    {A₀ A₁ : X.GradedAlgebraData} {B₀ B₁ : Y.GradedAlgebraData}
    (D : PullbackData g A₀ B₀) (a : A₁ ≅ A₀) (b : B₀ ≅ B₁) :
    PullbackData g A₁ B₁ where
  map {U' U} h := (b.hom.app U').comp ((D.map h).comp (a.hom.app U))
  isGradedBaseChangeAlong {U' U} h :=
    GradedRingHom.isGradedBaseChangeAlong_transport _ _ (D.isGradedBaseChangeAlong h)
      (a.hom.app U) (gradedAlgebraSectionRingEquiv a U).bijective (a.hom.app_algebraMap U)
      (b.hom.app U') (gradedAlgebraSectionRingEquiv b U').bijective (b.hom.app_algebraMap U')
  res_map := by
    intro U' V' U h' h x
    simp only [GradedRingHom.comp_apply]
    rw [← b.hom.naturality, D.res_map]
  map_res := by
    intro U' U V h hUV x
    simp only [GradedRingHom.comp_apply]
    rw [a.hom.naturality, D.map_res]

end AlgebraicGeometry.Scheme.GradedAlgebraData
