/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import WeilConjectures.CategoryTheory.ColimitSiteStageImage
import all WeilConjectures.CategoryTheory.ColimitSiteSetSectionEventualEquality
import WeilConjectures.CategoryTheory.StageSectionTransitionExistence
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionMatchingLift

/-! Existence of stage-image amalgamations on finite mapped stage covers.
Source: Stacks Project, Sites, Tag 0A35.
(blueprint: aux-colimit-site-stage-image-cover-amalgamation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, the finite-cover equalizer argument.
(blueprint: aux-colimit-site-stage-image-cover-amalgamation).

Proof: The cover R is finite by hfinite. Choose stage presentations of its finitely
many section values using the definition of colimitSiteStageImage. Lift their
presenting objects and arrows, together with the cover, to one stage above i and j
using the object and arrow colimit hypotheses and filteredness. Stage adjunctions
identify the maps α with the canonical comparison maps: their composites with the
units agree by hα, and adjunction makes those composites determine the maps.
Equality in the limit inverse-image sheaf is locally equality of presheaf
representatives. The exact description hQ of covers, finite composition, and
hfinite let these local equalities be witnessed by finite stage covers. Lift
those witnesses to a common stage as well. Stage sheaf separatedness then makes
the finitely many matching equations hold on the pairwise covering pullbacks.
These pullbacks are preserved by hpullback and
hVpullback. Equivalently, use that filtered colimits commute with the finite
matching-family equalizer, as in Tag 0A35. The transported cover remains covering
by hcover. The sheaf at that stage therefore glues the family to a section z.
Its image under α, restricted along the presentation of the cover's target,
belongs to colimitSiteStageImage by construction and restricts to each value of x.
For the empty cover the equalizer is the terminal set; the stage sheaf supplies
its unique section by the same argument. Only existence on a mapped stage cover
is asserted here; uniqueness and passage to the generated topology are separate.
-/
theorem colimit_site_stage_image_cover_exists_amalgamation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X)
    (x : (R.map (V.ι.app j).toFunctor).FamilyOfElements
      (colimitSiteStageImage F P V Q i G α).toFunctor) (hx : x.Compatible) :
    ∃ z, x.IsAmalgamation z := by
  classical
  obtain ⟨θ, hθ⟩ := stage_section_transition_existence J F P i
  let θG := fun t t' b ↦ (θ t t' b).app G
  have hθG := hθ G
  obtain ⟨B, β, γ, hβ, hβmap, hγ⟩ := colimit_site_raw_section_diagram
    J F P V Q i G α hα θG hθG
  have hB := colimit_site_raw_section_isSheaf J F P hfinite hcover hpullback
    V hobjects harrows Q hQ hVpullback i G θG hθG B β hβ hβmap
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let φ : colimit B ⟶ H.obj := colimit.desc B (Cocone.mk H.obj γ)
  have hγiso (t : Under i) :
      IsIso ((presheafToSheaf Q.toGrothendieck (Type u)).map (γ.app t)) := by
    have : (B.obj t).IsLeftKanExtension (β t) := hβ t
    apply raw_comparison_iso (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor
      (V.ι.app i).toFunctor (P i).toGrothendieck (P t.right).toGrothendieck
      Q.toGrothendieck (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
      (B.obj t) (β t) (γ.app t) (α t)
    · ext X x
      exact congrArg (fun k ↦ k x) (hγ t X.unop)
    · exact hα t
  have : IsConnected (Under i) := IsFiltered.isConnected (Under i)
  have : IsIso ((presheafToSheaf Q.toGrothendieck (Type u)).map φ) :=
    raw_colimit_comparison_iso Q.toGrothendieck B H.obj γ
  have : IsIso (sheafifyMap Q.toGrothendieck φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf Q.toGrothendieck (Type u)).map
      ((presheafToSheaf Q.toGrothendieck (Type u)).map φ)))
  have : IsIso (toSheafify Q.toGrothendieck (colimit B)) :=
    isIso_toSheafify Q.toGrothendieck hB
  have : IsIso (toSheafify Q.toGrothendieck H.obj) :=
    isIso_toSheafify Q.toGrothendieck H.property
  have : IsIso (φ ≫ toSheafify Q.toGrothendieck H.obj) := by
    rw [toSheafify_naturality]
    infer_instance
  have : IsIso φ :=
    IsIso.of_isIso_comp_right φ (toSheafify Q.toGrothendieck H.obj)
  let x' : (R.map (V.ι.app j).toFunctor).FamilyOfElements (colimit B) :=
    fun {Y} f hf ↦ (inv φ).app (op Y) (x f hf).val
  have hx' : x'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    change (colimit B).map g₁.op ((inv φ).app (op Y₁) (x f₁ hf₁).val) =
      (colimit B).map g₂.op ((inv φ).app (op Y₂) (x f₂ hf₂).val)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg ((inv φ).app (op Z)) (congrArg Subtype.val (hx g₁ g₂ hf₁ hf₂ heq))
  obtain ⟨t, W, T, hTcover, e, hT, y, hy, himage⟩ :=
    colimit_site_raw_section_matching_lift J F P hfinite hcover hpullback
      V hobjects harrows Q hVpullback i G θG hθG B β hβ hβmap j X R hR x' hx'
  let L := (sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  have hL : Presieve.IsSheaf (P t.right).toGrothendieck L.obj :=
    (isSheaf_iff_isSheaf_of_type _ L.obj).mp L.property
  obtain ⟨w, hw, _⟩ := hL.isSheafFor_of_mem_precoverage hTcover y hy
  let z := H.obj.map (eqToHom e.symm).op ((α t).hom.app (op W) w)
  have hz : z ∈ (colimitSiteStageImage F P V Q i G α).obj
      (op ((V.ι.app j).toFunctor.obj X)) := ⟨t, W, eqToHom e.symm, w, rfl⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  intro Y f hf
  apply Subtype.ext
  change H.obj.map f.op z = (x f hf).val
  rw [← hT] at hf
  cases hf with
  | mk p =>
    have hn := NatTrans.naturality_apply (α t).hom p.val.2.op w
    change (α t).hom.app (op p.val.1) (L.obj.map p.val.2.op w) =
      H.obj.map ((V.ι.app t.right).toFunctor.map p.val.2).op
        ((α t).hom.app (op W) w) at hn
    rw [hw p.val.2 p.property] at hn
    have hp := congrArg (φ.app (op ((V.ι.app t.right).toFunctor.obj p.val.1)))
      (himage p)
    have hφ (t : Under i) : colimit.ι B t ≫ φ = γ.app t := colimit.ι_desc _ _
    have hφapp := NatTrans.congr_app (hφ t)
      (op ((V.ι.app t.right).toFunctor.obj p.val.1))
    change (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj p.val.1)) ≫
      φ.app (op ((V.ι.app t.right).toFunctor.obj p.val.1)) =
        (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj p.val.1)) at hφapp
    have hγp := hγ t p.val.1
    change (β t).app (op p.val.1) ≫ (γ.app t).app
      (op ((V.ι.app t.right).toFunctor.obj p.val.1)) =
        (α t).hom.app (op p.val.1) at hγp
    have hcancel : (inv φ).app (op ((V.ι.app t.right).toFunctor.obj p.val.1)) ≫
        φ.app (op ((V.ι.app t.right).toFunctor.obj p.val.1)) = 𝟙 _ :=
      NatTrans.congr_app (IsIso.inv_hom_id φ) _
    dsimp [x'] at hp
    simp only [← types_comp_apply, Category.assoc, hφapp, hγp, hcancel,
      types_id_apply] at hp
    calc
      H.obj.map (((V.ι.app t.right).toFunctor.map p.val.2 ≫ eqToHom e).op) z =
          H.obj.map ((V.ι.app t.right).toFunctor.map p.val.2).op
            ((α t).hom.app (op W) w) := by
        dsimp [z]
        simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc,
          eqToHom_trans, eqToHom_refl, Category.comp_id]
      _ = (α t).hom.app (op p.val.1) (y p.val.2 p.property) := hn.symm
      _ = _ := hp

end CategoryTheory
