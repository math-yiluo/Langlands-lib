/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionCompatibility
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback

import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1PullSectionGeneric

/-! Conjugated form of the untwisted diagonal restriction. -/

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

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPushforward

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.leftDerivedUpperStarComp CondensedRing.leftDerivedUpperStarId

/-- The native compositor with its endpoints fixed to the public functor names. -/
@[no_expose]
private def pullComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f := by
  unfold moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp Λ f g

/-- The native identity comparison with its endpoint fixed to the public functor name. -/
@[no_expose]
private def pullId
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 (DerivedCategory (Modules Λ X)) := by
  unfold moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarId Λ X

/-- Associativity, using only the fixed functor endpoints. -/
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

/-- The left identity law, using only the fixed functor endpoints. -/
private theorem pullComp_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (q : X ⟶ Y)
    (K : DerivedCategory (Modules Λ Y)) :
    (pullComp Λ (𝟙 X) q).hom.app K ≫
      (pullId Λ X).hom.app ((moduleObjectDerivedPullback Λ q).obj K) =
        eqToHom (by rw [Category.id_comp]; rfl) := by
  unfold pullComp pullId moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp_id_left_app Λ q K

attribute [local irreducible] moduleObjectDerivedPullback pullComp pullId

attribute [local semireducible] moduleObjectDerivedPullback in
/-- The ambient comparison expressed through the fixed compositor wrappers. -/
private theorem ambient_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    ambientPullbackComparison Λ sq = (pullComp Λ f' g).symm ≪≫
      eqToIso (congrArg (fun t : X' ⟶ Y ↦ moduleObjectDerivedPullback Λ t)
        sq.toCommSq.w.symm) ≪≫ pullComp Λ g' f := by
  unfold ambientPullbackComparison CondensedRing.condensedAmbientPullbackComparison
    pullComp moduleObjectDerivedPullback
  rfl

attribute [local semireducible] moduleObjectDerivedPullback in
/-- The projective section is the same canonical comparison on arbitrary schemes. -/
private theorem section_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    pullSectionIso Λ Y f h = canonicalSection (fun X ↦ DerivedCategory (Modules Λ X))
      (fun {_ _} t ↦ moduleObjectDerivedPullback Λ t)
      (fun {_ _ _} f g ↦ pullComp Λ f g) (pullId Λ) (diagonalImmersion Y) f h := by
  unfold canonicalSection pullComp pullId
  exact pullSectionIso_eq Λ Y f h

/-- The square calculation before specializing the coefficient ring. -/
private theorem projective_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ (diagonalImmersion Y)).map
        ((ambientPullbackComparison Λ (square Y)).symm.app K).inv =
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback Λ
          (ProjectiveLine Y ↘ Y)).obj K) ≫
      (pullSectionIso Λ Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).inv.app
        ((moduleObjectDerivedPullback Λ
          (ProjectiveLine Y ↘ Y)).obj K) := by
  have h₁ : diagonalImmersion Y ≫ firstProjection Y = 𝟙 _ := by
    unfold firstProjection
    exact pullback.diagonal_fst _
  have h₂ : diagonalImmersion Y ≫ secondProjection Y = 𝟙 _ := by
    unfold secondProjection
    exact pullback.diagonal_snd _
  exact contravariantPullSectionSquare
    (fun X ↦ DerivedCategory (Modules Λ X)) (fun f ↦ moduleObjectDerivedPullback Λ f)
    (fun f g ↦ pullComp Λ f g) (pullId Λ)
    (fun f g h K ↦ pullComp_assoc Λ f g h K) (fun q K ↦ pullComp_unit Λ q K)
    (diagonalImmersion Y) (firstProjection Y) (secondProjection Y)
    (ProjectiveLine Y ↘ Y) h₁ h₂ (square Y).toCommSq.w.symm
    (ambientPullbackComparison Λ (square Y))
    (pullSectionIso Λ Y (firstProjection Y) h₁)
    (pullSectionIso Λ Y (secondProjection Y) h₂)
    (ambient_eq Λ (square Y)) (section_eq Λ Y (firstProjection Y) h₁)
    (section_eq Λ Y (secondProjection Y) h₂) K

/-- On the diagonal, the pulled-back ambient comparison is the second-projection pull-section
isomorphism followed by the inverse of the first-projection one. -/
theorem second_pull_section_core_conjugate
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).inv.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) := by
  have _ := hpl
  exact projective_square (coefficient l c).X Y K

end AlgebraicGeometry.ProEtale.RationalP1
