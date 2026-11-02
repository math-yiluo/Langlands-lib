import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction

/-! # The specified direct-image comparison for restriction to an open -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-- The restriction comparison expressed with actual pullback functors. -/
def openDirectImageBaseChangeIso (M : X.Modules) :
    (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward (f ∣_ V)).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M) :=
  ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
    ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
      ((restrictPushforwardIso f V).app M).symm ≪≫
      (Scheme.Modules.pushforward (f ∣_ V)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M)

/-- The ordinary restriction comparison is the adjunct of the restriction unit. -/
lemma restrictPushforwardIso_inv_adjoint (M : X.Modules) :
    (Scheme.Modules.restrictAdjunction V.ι).homEquiv _ _
      ((restrictPushforwardIso f V).inv.app M) =
    (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app M) ≫
      (pushforwardSquareIso V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι
        (isPullback_morphismRestrict f V).w.symm).hom.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Category.comp_id, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [restrictPushforwardIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app]
  change M.presheaf.map _ (M.presheaf.map _ m) =
    M.presheaf.map _ (M.presheaf.map _ m)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- The actual base-change map for an open restriction is the restriction isomorphism. -/
theorem pushforwardBaseChange_morphismRestrict (M : X.Modules) :
    pushforwardBaseChange V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι
      (isPullback_morphismRestrict f V).w.symm M =
    (openDirectImageBaseChangeIso f V M).hom := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app
    ((Scheme.Modules.pushforward f).obj M))).1
  simp only [openDirectImageBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Iso.hom_inv_id_app_assoc]
  apply ((Scheme.Modules.restrictAdjunction V.ι).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (Scheme.Modules.restrictAdjunction V.ι).homEquiv _ _
      (((Scheme.Modules.restrictAdjunction V.ι).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction V.ι)).hom.app _) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, pushforwardBaseChange, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, restrictPushforwardIso_inv_adjoint]
  have hn := (pushforwardSquareIso V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι
    (isPullback_morphismRestrict f V).w.symm).hom.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  rw [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.unit_leftAdjointUniq_hom_app]

/-- Base change to an open of the base is invertible for every module sheaf. -/
instance isIso_pushforwardBaseChange_morphismRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens) (M : X.Modules) :
    IsIso (pushforwardBaseChange V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι
      (isPullback_morphismRestrict f V).w.symm M) := by
  rw [pushforwardBaseChange_morphismRestrict]
  infer_instance

end Langlands.AlgebraicGeometry.Modules.DerivedSections
