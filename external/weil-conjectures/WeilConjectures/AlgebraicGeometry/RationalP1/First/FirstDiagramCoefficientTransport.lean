/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison

/-! # Canonical first-projection section and path comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local implicit_reducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local implicit_reducible] firstProjection
attribute [local irreducible] secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

/-- Canonical diagram transport commutes with a coefficient arrow. -/
theorem first_diagram_coefficient_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    {B N : DerivedCategory (Modules Λ (diagonalSurface Y))} (α : B ⟶ N)
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N) :
    (firstDiagramPushIso Λ Y L d).hom.app B ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map α =
    d.R₁.R.map α ≫ (eqToIso d.p₁_canonical).hom.app N ≫
      eqToHom ((congrArg (fun F ↦ F.obj N) d.p₁_canonical).symm.trans hobj) := by
  rw [← (firstDiagramPushIso Λ Y L d).hom.naturality α]
  simp only [firstDiagramPushIso, eqToIso.hom, eqToHom_app,
    eqToHom_trans]

end AlgebraicGeometry.ProEtale.RationalP1
