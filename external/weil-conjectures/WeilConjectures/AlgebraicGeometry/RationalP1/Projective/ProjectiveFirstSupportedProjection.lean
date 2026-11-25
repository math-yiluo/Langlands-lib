/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstCanonicalSectionProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSupportedSource
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveProjectionNaturalityRight

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
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

private theorem section_forward_supported
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (S : D ⥤ C) (M U : C) (V W B J : D)
    (e : U ≅ 𝟙_ C) (sM : M ⟶ S.obj J) (sU : U ⟶ S.obj W)
    (d : J ≅ V ⊗ W) (c : W ⟶ B) (z : U ⟶ S.obj B)
    (p : M ⊗ S.obj W ⟶ S.obj (V ⊗ W))
    (p' : M ⊗ S.obj B ⟶ S.obj (V ⊗ B))
    (hc : (ρ_ M).inv ≫ (M ◁ (e.inv ≫ sU)) ≫ p ≫ S.map d.inv = sM)
    (hn : (M ◁ S.map c) ≫ p' = p ≫ S.map (V ◁ c))
    (hz : z = sU ≫ S.map c) :
    sM ≫ S.map (d.hom ≫ (V ◁ c)) =
      (ρ_ M).inv ≫ (M ◁ (e.inv ≫ z)) ≫ p' := by
  rw [← hc, S.map_comp]
  simp only [Category.assoc, ← S.map_comp, d.inv_hom_id_assoc]
  rw [← hn, ← whiskerLeft_comp_assoc, hz]
  simp only [Category.assoc]

private theorem first_diagonal_tensor_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (diagonalTensorIso Λ Y M).inv =
      sectionTensorMap Λ (diagonalImmersion Y) (firstProjection Y)
        (pullSectionIso Λ Y (firstProjection Y)
          (by unfold firstProjection; exact pullback.diagonal_fst _))
        (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M := by
  simp only [diagonalTensorIso, Iso.symm_inv, asIso_hom, diagonalTensorMap]

/-- The first diagonal section and its tensor comparison evaluate on the supported unit. -/
theorem first_supported_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (firstPushSectionIso Λ Y).hom.app M ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
        ((diagonalTensorIso Λ Y M).hom ≫
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
            (supportedUnitIso Λ Y).hom)) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
        (firstDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)))) ≫
      projectionMap Λ (firstProjection Y) M
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) := by
  let : MonoidalCategory (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
    internalMonoidal Λ (ProjectiveLine Y)
  let : MonoidalCategory (DerivedCategory (Modules Λ (diagonalSurface Y))) :=
    internalMonoidal Λ (diagonalSurface Y)
  have hc := first_canonical_section_projection Λ Y M
  rw [← first_diagonal_tensor_inv] at hc
  exact section_forward_supported
    (moduleObjectDerivedPushforward Λ (firstProjection Y)) M
    (unit Λ (ProjectiveLine Y))
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
    ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj
      (unit Λ (ProjectiveLine Y)))
    ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj (source Λ Y))
    ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M)
    (singleUnitIso Λ (ProjectiveLine Y))
    ((firstPushSectionIso Λ Y).hom.app M)
    ((firstPushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)))
    (diagonalTensorIso Λ Y M) (supportedUnitIso Λ Y).hom
    (d.support₁.hom ≫ (firstDiagramPushIso Λ Y L d).hom.app _)
    (projectionMap Λ (firstProjection Y) M _)
    (projectionMap Λ (firstProjection Y) M _) hc
    (projectionMap_naturality_right Λ (firstProjection Y) M (supportedUnitIso Λ Y).hom)
    (first_supported_source Λ Y L d)

end AlgebraicGeometry.ProEtale.RationalP1
