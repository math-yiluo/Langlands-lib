/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Canonical sections of inverse images along an inverse system -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The displayed comparison, before taking sections. -/
private noncomputable def sectionComparison {R X Y : Scheme.{u}}
    (Λ : Type (u + 1)) [CommRing Λ] (h : X ⟶ Y) (f : Y ⟶ R)
    (g : X ⟶ R) (w : g = h ≫ f)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) g).obj
        ((upperStar (ModuleCat.{u + 1} Λ) g).obj G) :=
  (lowerStar (ModuleCat.{u + 1} Λ) f).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) h f g w).hom.app _ ≫
    (lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) h f g w).inv.app G)

/-- The identity comparisons cancel the identity adjunction unit. -/
private theorem sectionComparison_id {R X : Scheme.{u}}
    (Λ : Type (u + 1)) [CommRing Λ] (f : X ⟶ R)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    sectionComparison Λ (𝟙 X) f f (Category.id_comp f).symm G = 𝟙 _ := by
  dsimp [sectionComparison]
  rw [lowerStarComp_id_left, upperStarComp_id_left]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app]
  dsimp
  simp only [Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hn := (lowerStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    ((upperStarId (ModuleCat.{u + 1} Λ) X).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) f).obj G))
  dsimp at hn
  rw [← hn, ← Category.assoc,
    upperStarId_hom_app_unit_app, Iso.inv_hom_id_app]
  dsimp
  exact (lowerStar (ModuleCat.{u + 1} Λ) f).map_id _

/-- Naturality and the two associativity laws give composition of comparisons. -/
private theorem sectionComparison_comp {R X Y Z : Scheme.{u}}
    (Λ : Type (u + 1)) [CommRing Λ] (f : X ⟶ R) (h : Y ⟶ X) (k : Z ⟶ Y)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    sectionComparison Λ h f (h ≫ f) rfl G ≫
        sectionComparison Λ k (h ≫ f) (k ≫ h ≫ f) rfl G =
      sectionComparison Λ (k ≫ h) f (k ≫ h ≫ f) (Category.assoc k h f).symm G := by
  dsimp [sectionComparison]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) k).unit.naturality
    ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G)
  dsimp at hn
  rw [hn, Functor.map_comp, Category.assoc]
  have hn₂ := (lowerStarComp (ModuleCat.{u + 1} Λ) k (h ≫ f)).hom.naturality
    ((upperStar (ModuleCat.{u + 1} Λ) k).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) h f).inv.app G))
  dsimp at hn₂
  rw [reassoc_of% hn₂]
  have hn₃ := (lowerStarComp (ModuleCat.{u + 1} Λ) h f).hom.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) k).unit.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)))
  dsimp at hn₃
  rw [← reassoc_of% hn₃]
  have ha := congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} Λ) k h f
    (k ≫ h) (h ≫ f) (k ≫ h ≫ f) rfl rfl (Category.assoc k h f).symm)
    ((upperStar (ModuleCat.{u + 1} Λ) k).obj
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)))
  dsimp at ha
  rw [← reassoc_of% ha]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hu := upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) k h
    ((upperStar (ModuleCat.{u + 1} Λ) f).obj G)
  rw [Adjunction.comp_unit_app] at hu
  rw [← hu, Functor.map_comp, Category.assoc]
  have hn₄ := (lowerStarComp (ModuleCat.{u + 1} Λ) (k ≫ h) f
    (k ≫ h ≫ f) (Category.assoc k h f).symm).hom.naturality
    ((upperStarComp (ModuleCat.{u + 1} Λ) k h).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) f).obj G))
  dsimp at hn₄
  rw [reassoc_of% hn₄]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  have ha₂ := congr_app (congrArg Iso.inv
    (upperStarComp_assoc (ModuleCat.{u + 1} Λ) k h f)) G
  dsimp at ha₂
  simp only [Category.id_comp] at ha₂
  simp only [Category.assoc]
  rw [ha₂]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- The composition equation with named composites, for diagrams and cones. -/
private theorem sectionComparison_comp_named {R X Y Z : Scheme.{u}}
    (Λ : Type (u + 1)) [CommRing Λ] (f : X ⟶ R) (h : Y ⟶ X) (k : Z ⟶ Y)
    (g : Y ⟶ R) (g' : Z ⟶ R) (kh : Z ⟶ X)
    (wg : g = h ≫ f) (wg' : g' = k ≫ g) (wkh : kh = k ≫ h)
    (w : g' = kh ≫ f)
    (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    sectionComparison Λ h f g wg G ≫ sectionComparison Λ k g g' wg' G =
      sectionComparison Λ kh f g' w G := by
  subst g
  subst g'
  subst kh
  exact sectionComparison_comp Λ f h k G

/-- The adjunction units, corrected by direct- and inverse-image composition, form a
section diagram and a cocone on any tail of an inverse system. No affineness or
continuity assertion is needed for this coherence statement.

Source: Stacks Project, Etale Cohomology, Lemma 09YU (lemma-category-is-colimit),
proof, Fully faithful; the coherence argument is steps 2, 5 and 6 of the parent node.
(blueprint: lem-weil-pbc-pullback-sections-diagram)

Proof: Take the section module S_i at each stage and the displayed map mu_f on arrows.
The unit equation characterizing the inverse-image composition isomorphism identifies
mu_f with the unit for the composite morphism, transported through direct image.
Naturality of the unit and associativity of the direct-image composition then give
mu_g mu_f = mu_(fg). The identity composition comparison cancels the identity unit,
so mu_id = id. The same unit equation with the limit projection, and the cone equation,
gives tau_j mu_f = tau_i. Thus these objects and arrows define a functor F, the tau_i
define a cocone B, and the object comparisons e_i and eB can all be chosen as identities.
For module coefficients the units and composition maps are already module morphisms;
uniqueness of the adjoint comparison gives these same equations without forgetting the
module structure. This is only the coherence part, and asserts no colimit property. -/
theorem exists_pullbackSections_diagram {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) :
    let J := {i : I // i₀ ≤ i}
    let S : J → ModuleCat.{u + 1} Λ := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)).obj.obj
          (op V₀)
    let T : ModuleCat.{u + 1} Λ := ((lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
      ((upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀)
    let μ : ∀ {i j : J}, (i ⟶ j) → (S i ⟶ S j) := fun {i j} f ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ)
          (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
          (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE j.property).op)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
            (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
    let τ : ∀ i : J, S i ⟶ T := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
          (D.map (homOfLE i.property).op) (c.π.app (op i₀))
          (c.w (homOfLE i.property).op).symm).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
            (D.map (homOfLE i.property).op) (c.π.app (op i₀))
            (c.w (homOfLE i.property).op).symm).inv.app G)).hom.app (op V₀)
    ∃ (F : J ⥤ ModuleCat.{u + 1} Λ) (B : Cocone F)
      (e : ∀ i : J, F.obj i ≅ S i) (eB : B.pt ≅ T),
      (∀ (i j : J) (f : i ⟶ j), (e i).inv ≫ F.map f ≫ (e j).hom = μ f) ∧
      (∀ i : J, (e i).inv ≫ B.ι.app i ≫ eB.hom = τ i) := by
  intro J S T μ τ
  have hid (i : J) : μ (𝟙 i) = 𝟙 (S i) := by
    change (sectionComparison Λ
      (D.map (homOfLE (show i.val ≤ i.val from leOfHom (𝟙 i))).op)
      (D.map (homOfLE i.property).op) (D.map (homOfLE i.property).op) _ G).hom.app
        (op V₀) = _
    have hi : (homOfLE (show i.val ≤ i.val from leOfHom (𝟙 i))).op = 𝟙 (op i.val) :=
      Subsingleton.elim _ _
    simp only [hi, D.map_id]
    have hh := sectionComparison_id Λ (D.map (homOfLE i.property).op) G
    exact congrArg (fun q ↦ q.hom.app (op V₀)) hh
  have hcomp (i j k : J) (f : i ⟶ j) (g : j ⟶ k) : μ f ≫ μ g = μ (f ≫ g) := by
    have hh := sectionComparison_comp_named Λ
      (D.map (homOfLE i.property).op)
      (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
      (D.map (homOfLE (show j.val ≤ k.val from leOfHom g)).op)
      (D.map (homOfLE j.property).op) (D.map (homOfLE k.property).op)
      (D.map (homOfLE (show i.val ≤ k.val from leOfHom (f ≫ g))).op)
      (by rw [← D.map_comp]; rfl) (by rw [← D.map_comp]; rfl)
      (by rw [← D.map_comp]; rfl) (by rw [← D.map_comp]; rfl) G
    exact congrArg (fun q ↦ q.hom.app (op V₀)) hh
  have htau (i j : J) (f : i ⟶ j) : μ f ≫ τ j = τ i := by
    have hh := sectionComparison_comp_named Λ
      (D.map (homOfLE i.property).op)
      (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
      (c.π.app (op j.val)) (D.map (homOfLE j.property).op)
      (c.π.app (op i₀)) (c.π.app (op i.val))
      (by rw [← D.map_comp]; rfl) (c.w (homOfLE j.property).op).symm
      (c.w (homOfLE (show i.val ≤ j.val from leOfHom f)).op).symm
      (c.w (homOfLE i.property).op).symm G
    exact congrArg (fun q ↦ q.hom.app (op V₀)) hh
  let F : J ⥤ ModuleCat.{u + 1} Λ :=
    { obj := S
      map := fun f ↦ μ f
      map_id := hid
      map_comp := fun f g ↦ (hcomp _ _ _ f g).symm }
  let B : Cocone F :=
    { pt := T
      ι := { app := τ
             naturality := fun i j f ↦ by
               dsimp [F]
               simpa only [Category.comp_id] using htau i j f } }
  refine ⟨F, B, (fun _ ↦ Iso.refl _), Iso.refl _, ?_, ?_⟩
  · intro i j f
    simp [F]
  · intro i
    change 𝟙 (S i) ≫ τ i ≫ 𝟙 T = τ i
    simp only [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Etale
