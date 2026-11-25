/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1PullSectionGeneric

/-! # First-projection diagonal section normalization -/

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

attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] pushSectionIso
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.mapDerivedCategory
attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
attribute [local irreducible] CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] CondensedRing.leftDerivedUpperStarId

/-- The native adjunction with the public functor endpoints fixed explicitly. -/
@[no_expose]
private def pathAdj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ f ⊣ moduleObjectDerivedPushforward Λ f := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

private def pullComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f := by
  unfold moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp Λ f g

private def pullId
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    moduleObjectDerivedPullback Λ (𝟙 X) ≅
      𝟭 (DerivedCategory (Modules Λ X)) := by
  unfold moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarId Λ X

private theorem pullComp_assoc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X W V Y : Scheme.{u}}
    (d : X ⟶ W) (f : W ⟶ V) (q : V ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) :
    (pullComp Λ (d ≫ f) q).hom.app K ≫
        (pullComp Λ d f).hom.app ((moduleObjectDerivedPullback Λ q).obj K) =
      eqToHom (by rw [Category.assoc]) ≫
        (pullComp Λ d (f ≫ q)).hom.app K ≫
        (moduleObjectDerivedPullback Λ d).map ((pullComp Λ f q).hom.app K) := by
  unfold pullComp moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp_assoc_app Λ d f q K

private theorem pullComp_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (q : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) :
    (pullComp Λ (𝟙 X) q).hom.app K ≫
      (pullId Λ X).hom.app ((moduleObjectDerivedPullback Λ q).obj K) =
        eqToHom (by rw [Category.id_comp]; rfl) := by
  unfold pullComp pullId moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp_id_left_app Λ q K

private theorem projective_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).map
        ((condensedAmbientPullbackComparison Λ (square Y)).symm.app K).inv =
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ≫
      (pullSectionIso Λ Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).inv.app
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) := by
  have h₁ : diagonalImmersion Y ≫ firstProjection Y = 𝟙 _ := by
    unfold firstProjection
    exact pullback.diagonal_fst _
  have h₂ : diagonalImmersion Y ≫ secondProjection Y = 𝟙 _ := by
    unfold secondProjection
    exact pullback.diagonal_snd _
  exact contravariantPullSectionSquare
    (fun X ↦ DerivedCategory (Modules Λ X))
    (fun {_ _} t ↦ moduleObjectDerivedPullback Λ t)
    (fun f g ↦ pullComp Λ f g) (pullId Λ)
    (fun f g h K ↦ pullComp_assoc Λ f g h K)
    (fun q K ↦ pullComp_unit Λ q K)
    (diagonalImmersion Y) (firstProjection Y) (secondProjection Y)
    (ProjectiveLine Y ↘ Y) h₁ h₂ (square Y).toCommSq.w.symm
    (condensedAmbientPullbackComparison Λ (square Y))
    (pullSectionIso Λ Y (firstProjection Y) h₁)
    (pullSectionIso Λ Y (secondProjection Y) h₂)
    (by rfl) (by exact pullSectionIso_eq Λ Y (firstProjection Y) h₁)
    (by exact pullSectionIso_eq Λ Y (secondProjection Y) h₂) K

private theorem inverse_section_eq {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {X Y : C} {Z : D} (A : X ≅ Y)
    (s₁ : G.obj Y ≅ Z) (s₂ : G.obj X ≅ Z)
    (h : G.map A.hom = s₂.hom ≫ s₁.inv) :
    G.map A.inv ≫ s₂.hom = s₁.hom := by
  apply (cancel_epi (G.map A.hom)).1
  rw [← G.map_comp_assoc, A.hom_inv_id, G.map_id, Category.id_comp, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The second section is the conjugate under the fixed public endpoints. -/
private theorem secondPush_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (pushSectionIso Λ Y).hom =
      (conjugateIsoEquiv Adjunction.id
        ((pathAdj Λ (secondProjection Y)).comp (pathAdj Λ (diagonalImmersion Y)))
        (pullSectionIso Λ Y (secondProjection Y)
          (by unfold secondProjection; exact pullback.diagonal_snd _))).hom := by
  unfold pushSectionIso pathAdj
  rfl

/-- The first section is the conjugate under the fixed public endpoints. -/
private theorem firstPush_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (firstPushSectionIso Λ Y).hom =
      (conjugateIsoEquiv Adjunction.id
        ((pathAdj Λ (firstProjection Y)).comp (pathAdj Λ (diagonalImmersion Y)))
        (pullSectionIso Λ Y (firstProjection Y)
          (by unfold firstProjection; exact pullback.diagonal_fst _))).hom := by
  unfold firstPushSectionIso derivedSection pathAdj
  rfl

/-- The path map is the conjugate of the inverse pullback comparison. -/
private theorem path_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (firstPathComparison Λ Y).hom =
      conjugateEquiv
        ((pathAdj Λ (ProjectiveLine Y ↘ Y)).comp (pathAdj Λ (secondProjection Y)))
        ((pathAdj Λ (ProjectiveLine Y ↘ Y)).comp (pathAdj Λ (firstProjection Y)))
        (condensedAmbientPullbackComparison Λ (square Y)).inv := by
  unfold firstPathComparison pathAdj
  rfl

/-- Transport a section equation through three equalities of natural transformations. -/
private theorem transport_path_section
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (J : C ⥤ E) (P₁ P₂ : E ⥤ C)
    (s₁ : 𝟭 C ⟶ J ⋙ P₁) (s₂ : 𝟭 C ⟶ J ⋙ P₂)
    (t : P₂ ⋙ R ⟶ P₁ ⋙ R)
    {s₁' : 𝟭 C ⟶ J ⋙ P₁} {s₂' : 𝟭 C ⟶ J ⋙ P₂}
    {t' : P₂ ⋙ R ⟶ P₁ ⋙ R}
    (h₁ : s₁ = s₁') (h₂ : s₂ = s₂') (ht : t = t')
    (h : Functor.whiskerRight s₂' R ≫ Functor.whiskerLeft J t' =
      Functor.whiskerRight s₁' R) (M : C) :
    R.map (s₂.app M) ≫ t.app (J.obj M) = R.map (s₁.app M) := by
  subst s₁ s₂ t
  exact NatTrans.congr_app h M

-- Normalize the fixed comparisons through generic equality transport.
/-- Changing the two direct-image paths carries the second diagonal section to the first. -/
theorem first_path_section
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        ((pushSectionIso Λ Y).hom.app M) ≫
      (firstPathComparison Λ Y).hom.app
        ((moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M) =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      ((firstPushSectionIso Λ Y).hom.app M) := by
  let q := ProjectiveLine Y ↘ Y
  let p₁ := firstProjection Y
  let p₂ := secondProjection Y
  let i := diagonalImmersion Y
  let aq := pathAdj Λ q
  let a₁ := pathAdj Λ p₁
  let a₂ := pathAdj Λ p₂
  let ai := pathAdj Λ i
  let c := (condensedAmbientPullbackComparison Λ (square Y)).symm
  have hc : Functor.whiskerRight c.hom (moduleObjectDerivedPullback Λ i) ≫
        Functor.whiskerLeft (moduleObjectDerivedPullback Λ q)
          (pullSectionIso Λ Y p₂
            (by unfold p₂ secondProjection; exact pullback.diagonal_snd _)).hom =
      Functor.whiskerLeft (moduleObjectDerivedPullback Λ q)
        (pullSectionIso Λ Y p₁
          (by unfold p₁ firstProjection; exact pullback.diagonal_fst _)).hom := by
    apply NatTrans.ext
    funext K
    dsimp only [q, p₁, p₂, i, c]
    have hs := projective_square Λ Y K
    let G := moduleObjectDerivedPullback Λ (diagonalImmersion Y)
    let A := condensedAmbientPullbackComparison Λ (square Y)
    let s₁ := pullSectionIso Λ Y (firstProjection Y)
      (by unfold firstProjection; exact pullback.diagonal_fst _)
    let s₂ := pullSectionIso Λ Y (secondProjection Y)
      (by unfold secondProjection; exact pullback.diagonal_snd _)
    exact inverse_section_eq G (A.app K)
      (s₁.app ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))
      (s₂.app ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)) hs
  have h := CategoryTheory.Adjunction.conjugate_section_comparison
    aq a₁ a₂ ai
    (pullSectionIso Λ Y p₁ (by unfold p₁ firstProjection; exact pullback.diagonal_fst _))
    (pullSectionIso Λ Y p₂ (by unfold p₂ secondProjection; exact pullback.diagonal_snd _)) c.hom hc
  exact transport_path_section
    (moduleObjectDerivedPushforward Λ q) (moduleObjectDerivedPushforward Λ i)
    (moduleObjectDerivedPushforward Λ p₁) (moduleObjectDerivedPushforward Λ p₂)
    (firstPushSectionIso Λ Y).hom (pushSectionIso Λ Y).hom (firstPathComparison Λ Y).hom
    (firstPush_conjugate Λ Y) (secondPush_conjugate Λ Y) (path_conjugate Λ Y) h M

end AlgebraicGeometry.ProEtale.RationalP1
