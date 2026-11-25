/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus

/-! # Monoidal restriction along a cocontinuous site functor

Source: Stacks, Tags 03CY, 03EK and 04B8.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe c v d z w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{z} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
  (a : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R ≅
    (F.sheafPushforwardContinuous RingCat.{w} J K).obj
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))

private noncomputable instance presheafRMonoidal :
    MonoidalCategory (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})))

private noncomputable instance presheafSMonoidal :
    MonoidalCategory (PresheafOfModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{w} (S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})))

private def restrictionSheafificationIso :
    PresheafOfModules.pushforward.{w} a.hom.hom ⋙
      PresheafOfModules.sheafification.{w}
        (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _) ≅
      PresheafOfModules.sheafification.{w}
        (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _) ⋙
        pushforward.{w} a.hom := by
  have hi P := restrictionSheafificationMap_isIso a.hom P
  refine NatIso.ofComponents (fun P ↦ asIso (restrictionSheafificationMap a.hom P)) ?_
  intro P Q f
  apply ((PresheafOfModules.sheafificationAdjunction.{w} (R :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)).homEquiv _ _).injective
  ext U x
  change (restrictionSheafificationMap a.hom Q).val.app U
      (((PresheafOfModules.sheafification.{w}
        (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)).map
          ((PresheafOfModules.pushforward.{w} a.hom.hom).map f)).val.app U
            (((PresheafOfModules.sheafificationAdjunction.{w}
              (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)).unit.app
                ((PresheafOfModules.pushforward.{w} a.hom.hom).obj P)).app U x)) =
    ((PresheafOfModules.sheafification.{w}
      (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _)).map f).val.app
        (F.op.obj U)
      ((restrictionSheafificationMap a.hom P).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w}
          (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)).unit.app
            ((PresheafOfModules.pushforward.{w} a.hom.hom).obj P)).app U x))
  rw [sheafification_unit_naturality_apply, restrictionSheafificationMap_unit_apply,
    restrictionSheafificationMap_unit_apply]
  exact congrArg (fun k ↦ k.app (F.op.obj U) x)
    ((PresheafOfModules.sheafificationAdjunction.{w}
      (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _)).unit.naturality f)

private theorem presheaf_isIso {E : Type*} [Category* E]
    {B : Eᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} B} (f : M ⟶ N)
    (h : ∀ U, IsIso (f.app U)) : IsIso f := by
  have (U : Eᵒᵖ) := h U
  exact inferInstanceAs (IsIso (PresheafOfModules.isoMk
    (fun U ↦ asIso (f.app U)) (fun {_ _} g ↦ f.naturality g)).hom)

private theorem restrictionUnit_isIso (B E : Type w) [CommRing B] [CommRing E]
    (f : B →+* E) (hf : Function.Bijective f) :
    IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars f)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (show B → E from
    Functor.LaxMonoidal.ε (ModuleCat.restrictScalars f))
  have h : (show B → E from Functor.LaxMonoidal.ε (ModuleCat.restrictScalars f)) = f :=
    funext (ModuleCat.restrictScalars_η f)
  rw [h]
  exact hf

@[instance_reducible] private def restrictionPresheafMonoidal :
    (PresheafOfModules.pushforward.{w} (F := F)
      (R := S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})
      (S := R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) a.hom.hom).Monoidal := by
  let G := PresheafOfModules.pushforward.{w} (F := F)
    (R := S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})
    (S := R.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) a.hom.hom
  letI : G.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal a.hom.hom
  have hε : IsIso (Functor.LaxMonoidal.ε G) := by
    apply presheaf_isIso
    intro U
    dsimp only [G]
    erw [PresheafOfModules.pushforward_ε_app a.hom.hom U]
    exact restrictionUnit_isIso (R.obj.obj U) (S.obj.obj (F.op.obj U))
      (a.hom.hom.app U).hom (ConcreteCategory.bijective_of_isIso (a.hom.hom.app U))
  have hμ (M N) : IsIso (Functor.LaxMonoidal.μ G M N) := by
    apply presheaf_isIso
    intro U
    dsimp only [G]
    erw [PresheafOfModules.pushforward_μ_app a.hom.hom M N U]
    exact WeilConjectures.SemilinearSections.restrictScalars_mu_isIso
      (R.obj.obj U) (S.obj.obj (F.op.obj U)) (a.hom.hom.app U).hom _ _
      (ConcreteCategory.bijective_of_isIso (a.hom.hom.app U))
  exact Functor.Monoidal.ofLaxMonoidal G

/-- Restriction with invertible scalar map along a continuous, cocontinuous functor is
strong monoidal, for the existing sheaf tensor products.
Source: Stacks, Modules on Sites, Tags 03CY and 03EK; Sites, Tag 04B8
(auxiliary; not a blueprint node).

Proof: the presheaf restriction is strong monoidal. Its unit is the invertible coefficient
map; its tensorator is the scalar-restriction tensorator, invertible by the semilinear
change-of-ring tensor equivalence. Module sheafification commutes with restriction:
restrict its unit and transpose under sheafification. Cocontinuity preserves the local
bijection, so the transpose is invertible. The unit naturality equation makes these maps
natural. Both sheafification functors are monoidal localizations; their universal property
therefore equips the sheaf restriction with a strong monoidal structure. The proof uses
no points, no nonzero-ring hypothesis and no equality of the site and coefficient universes.
-/
theorem ringed_cocontinuous_monoidal : Nonempty (pushforward.{w} a.hom).Monoidal := by
  let L := PresheafOfModules.sheafification.{w} (R :=
    (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) (𝟙 _)
  let H := pushforward.{w} a.hom
  let P : PresheafOfModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj ⥤
      PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj :=
    PresheafOfModules.pushforward.{w} a.hom.hom
  let T := PresheafOfModules.sheafification.{w} (R :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) (𝟙 _)
  let W := K.W.inverseImage (PresheafOfModules.toPresheaf.{w}
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj)
  let : P.Monoidal := restrictionPresheafMonoidal F R S a
  let : L.Monoidal := inferInstance
  let : T.Monoidal := inferInstance
  let : Localization.Lifting L W (P ⋙ T) H :=
    ⟨(restrictionSheafificationIso F R S a).symm⟩
  exact ⟨Localization.Monoidal.functorMonoidalOfComp L W H (P ⋙ T)⟩

end SheafOfModules
