import Langlands.AlgebraicGeometry.Modules.OpenDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.SectionsBaseChangeComposition
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Mathlib.RingTheory.Localization.BaseChange

/-! # Sections localization from the specified scalar comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X X' : Scheme.{u}} {R T : CommRingCat.{u}}

/-- The specified invertible scalar comparison, on the ordinary algebra tensor product. -/
def scalarSectionsBaseChangeAlgebraEquiv [Algebra R T]
    (f : X ⟶ Spec R) (f' : X' ⟶ Spec T) (g : X' ⟶ X)
    (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (M : X.Modules)
    [IsIso (scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T)) f f' g w M)] :
    T ⊗[R] ((relativeGlobalSections f).obj M) ≃ₗ[T]
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M) :=
  (Langlands.Scheme.Modules.extendScalarsAlgebraEquiv R T
    ((relativeGlobalSections f).obj M)).symm ≪≫ₗ
      (asIso (scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T))
        f f' g w M)).toLinearEquiv

set_option maxHeartbeats 600000 in
/-- An invertible scalar sections comparison over a localization is a module localization. -/
lemma isLocalizedModule_sectionsBaseChangeMap [Algebra R T]
    (S : Submonoid R) [IsLocalization S T]
    (f : X ⟶ Spec R) (f' : X' ⟶ Spec T) (g : X' ⟶ X)
    (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (M : X.Modules)
    [IsIso (scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T)) f f' g w M)] :
    IsLocalizedModule S
      (sectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T)) f f' g w M).hom := by
  let eT := scalarSectionsBaseChangeAlgebraEquiv f f' g w M
  let e : T ⊗[R] ((relativeGlobalSections f).obj M) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R T)).obj
        ((relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M)) :=
    AddEquiv.toLinearEquiv eT.toAddEquiv <| by
      intro r x
      change eT (r • x) = algebraMap R T r • eT x
      rw [← IsScalarTower.algebraMap_smul T r x, map_smul]
  have he : IsLocalizedModule S
      (e.toLinearMap.comp
        (TensorProduct.mk R T ((relativeGlobalSections f).obj M) 1)) :=
    IsLocalizedModule.of_linearEquiv S _ e
  have hh : (sectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T))
      f f' g w M).hom = e.toLinearMap.comp
        (TensorProduct.mk R T ((relativeGlobalSections f).obj M) 1) := by
    ext x
    change ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x =
      scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R T)) f f' g w M
        ((1 : T) ⊗ₜ[R,algebraMap R T] x)
    exact (scalarSectionsBaseChangeMap_one_tmul
      (CommRingCat.ofHom (algebraMap R T)) f f' g w M x).symm
  rw [hh]
  exact he

/-- Under restriction-to-pullback, the pullback unit on sections is ordinary restriction. -/
lemma pullback_unit_app_comp_restrictFunctorIsoPullback_inv
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : X.Modules) (W : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app W ≫
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).app (j ⁻¹ᵁ W) =
      M.presheaf.map (homOfLE (j.image_preimage_le W)).op := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction j) (Scheme.Modules.pullbackPushforwardAdjunction j) M
  change (Scheme.Modules.restrictAdjunction j).unit.app M ≫
    (Scheme.Modules.pushforward j).map
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) = _ at h
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M) =
      (Scheme.Modules.restrictAdjunction j).unit.app M := by
    rw [← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] using
    congrArg (fun k => k.app W) hu

end Langlands.AlgebraicGeometry.Modules.DerivedSections
