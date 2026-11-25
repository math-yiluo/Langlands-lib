/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.ModuleSheafificationLocalIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Module sheafification and restriction along a morphism of sites

Source: Stacks Project, Sites, Tag 04B8, lemma-almost-cocontinuous-sheafification;
Modules on Sites, Tag 04IY, lemma-relocalize; used in Tag 099E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite
namespace PresheafOfModules
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{u})

/-- Restriction of module sheaves adds maps sectionwise.
Source: the definition of restriction.
(auxiliary; not a blueprint node). -/
instance moduleRestriction_additive :
    (SheafOfModules.pushforward (F := F)
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))).Additive :=
  ⟨fun {_ _} a b ↦ by ext X x; rfl⟩

private def restrictedRing : Sheaf J RingCat.{u} :=
  (F.sheafPushforwardContinuous RingCat.{u} J K).obj R

private def restrictionP : PresheafOfModules.{u} R.obj ⥤
    PresheafOfModules.{u} (restrictedRing (J := J) F R).obj :=
  pushforward (F := F) (𝟙 _)

private def restrictionS : SheafOfModules.{u} R ⥤
    SheafOfModules.{u} (restrictedRing (J := J) F R) :=
  SheafOfModules.pushforward (F := F) (𝟙 _)

private def restrictionUnit (M : PresheafOfModules.{u} R.obj) :
    (restrictionP (J := J) F R).obj M ⟶
      (SheafOfModules.forget _ ⋙ restrictScalars (𝟙 (restrictedRing (J := J) F R).obj)).obj
        ((restrictionS (J := J) F R).obj
          ((sheafification.{u} (J := K) (R := R) (R₀ := R.obj) (𝟙 R.obj)).obj M)) :=
  (restrictionP (J := J) F R).map
    ((sheafificationAdjunction (J := K) (R := R) (𝟙 R.obj)).unit.app M)

private theorem restrictionUnit_W (M : PresheafOfModules.{u} R.obj) :
    J.W ((toPresheaf _).map (restrictionUnit (J := J) F R M)) := by
  let η := CategoryTheory.toSheafify K M.presheaf
  change J.W (Functor.whiskerLeft F.op η)
  have : Presheaf.IsLocallyInjective J (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallyInjective_whisker J K F η
  have : Presheaf.IsLocallySurjective J (Functor.whiskerLeft F.op η) :=
    Presheaf.isLocallySurjective_whisker J K F η
  exact J.W_of_isLocallyBijective _

private theorem restrictionComparison_isIso (M : PresheafOfModules.{u} R.obj) :
    IsIso (((sheafificationAdjunction (𝟙 (restrictedRing (J := J) F R).obj)).homEquiv _ _).symm
      (restrictionUnit (J := J) F R M)) := by
  let adj := sheafificationAdjunction (𝟙 (restrictedRing (J := J) F R).obj)
  let S := sheafification (𝟙 (restrictedRing (J := J) F R).obj)
  have h := restrictionUnit_W (J := J) F R M
  have : IsIso (S.map (restrictionUnit (J := J) F R M)) := by
    change ((MorphismProperty.isomorphisms _).inverseImage S) _
    rw [← inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    exact h
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Module sheafification commutes with restriction along a continuous and cocontinuous
functor of small sites, with the canonical unit-compatible comparison.
Source: Stacks Project, Sites, Tag 04B8, lemma-almost-cocontinuous-sheafification,
and Modules on Sites, Tag 04IY, lemma-relocalize, as used in Tag 099E.
(auxiliary; not a blueprint node).

Proof: restrict the sheafification unit and transpose it under sheafification on the source
site. Cocontinuity preserves local bijectivity of the unit. Its transpose is an isomorphism:
it is the sheafification of that local bijection followed by an invertible counit. The unit
naturality equation proves naturality of the comparison. -/
theorem exists_moduleSheafificationRestrictionIso :
    ∃ z : pushforward (F := F) (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj) ⋙
        sheafification (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj) ≅
      sheafification.{u} (J := K) (R := R) (R₀ := R.obj) (𝟙 R.obj) ⋙
        SheafOfModules.pushforward (F := F)
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R)),
      ∀ (M : PresheafOfModules.{u} R.obj) (X : Cᵒᵖ)
        (x : M.obj (F.op.obj X)),
        ((z.app M).hom.val.app X)
          (((sheafificationAdjunction
            (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).unit.app
              ((pushforward (F := F) (𝟙 _)).obj M)).app X x) =
            ((sheafificationAdjunction (J := K) (R := R) (𝟙 R.obj)).unit.app M).app
              (F.op.obj X) x := by
  let P := restrictionP (J := J) F R
  let Q := restrictionS (J := J) F R
  let adj := sheafificationAdjunction (𝟙 (restrictedRing (J := J) F R).obj)
  let S := sheafification (𝟙 (restrictedRing (J := J) F R).obj)
  let t : P ⋙ S ⟶ sheafification.{u} (J := K) (R := R) (R₀ := R.obj) (𝟙 R.obj) ⋙ Q :=
    { app M := (adj.homEquiv _ _).symm (restrictionUnit (J := J) F R M)
      naturality := by
        intro M N f
        apply (adj.homEquiv _ _).injective
        simp only [Functor.comp_map]
        rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
        simp only [Equiv.apply_symm_apply]
        have h := (sheafificationAdjunction (J := K) (R := R) (𝟙 R.obj)).unit.naturality f
        ext X x
        exact congrArg (fun z ↦ z.app (F.op.obj X) x) h }
  have ht : IsIso t := (NatTrans.isIso_iff_isIso_app t).2
    (fun M => restrictionComparison_isIso (J := J) F R M)
  refine ⟨asIso t, ?_⟩
  intro M X x
  have h := (adj.homEquiv _ _).apply_symm_apply (restrictionUnit (J := J) F R M)
  exact congrArg (fun z ↦ z.app X x) h

/-- Maps from a restricted module sheafification are determined by original presheaf
unit sections on any covering locus of the source site.
Source: Stacks Project, Tag 04B8, lemma-almost-cocontinuous-sheafification, and Tag 099E.
(auxiliary; not a blueprint node).

Proof: precompose with the canonical unit-compatible restriction comparison. Use the
covering-locus hom-ext theorem for the source-site sheafification and its unit formula. -/
theorem restricted_sheafification_hom_ext
    (M : PresheafOfModules.{u} R.obj)
    (E : Cᵒᵖ → Prop)
    (hcover : ∀ X : C, ∃ S ∈ J X, ∀ (Y : C) (a : Y ⟶ X), S a → E (op Y))
    (N : SheafOfModules.{u} ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))
    (f g : (SheafOfModules.pushforward (F := F)
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))).obj
        ((sheafification.{u} (J := K) (R := R) (𝟙 R.obj)).obj M) ⟶ N)
    (h : ∀ (X : Cᵒᵖ), E X → ∀ x : M.obj (F.op.obj X),
      f.val.app X (((sheafificationAdjunction (J := K) (R := R)
        (𝟙 R.obj)).unit.app M).app (F.op.obj X) x) =
      g.val.app X (((sheafificationAdjunction (J := K) (R := R)
        (𝟙 R.obj)).unit.app M).app (F.op.obj X) x)) : f = g := by
  obtain ⟨z, hz⟩ := exists_moduleSheafificationRestrictionIso (J := J) F R
  apply (cancel_epi (z.app M).hom).1
  apply sheafification_hom_ext_on_locus
    ((pushforward (F := F) (𝟙 _)).obj M) E hcover N
  intro X hX x
  change f.val.app X ((z.app M).hom.val.app X _) =
    g.val.app X ((z.app M).hom.val.app X _)
  exact (congrArg (f.val.app X) (hz M X x)).trans
    ((h X hX x).trans (congrArg (g.val.app X) (hz M X x)).symm)

end PresheafOfModules
