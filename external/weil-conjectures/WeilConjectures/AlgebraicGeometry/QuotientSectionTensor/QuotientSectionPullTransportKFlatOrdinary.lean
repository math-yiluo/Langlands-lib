/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData

/-! # Ordinary square for flat-term quotient section pull transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The normalized ordinary section square is obtained by conjugating the
internal pullback scalar square through the two chosen ordinary section models. -/
theorem section_pull_transport_kflat_ordinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY) :
    ∃ e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E,
      ∀ M : Modules Λ Y,
        (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
            cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
            cX.model.E.map ((pullComparison Λ f).hom.app M) =
          (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
            (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
            e.hom.app ((equivalence Λ Y).functor.obj M) := by
  have _ := hcX
  have _ := hcY
  let d : (equivalence Λ Y).functor ⋙ (cY.model.E ⋙ pullback Λ' f) ≅
      (equivalence Λ Y).functor ⋙ (pullback Λ f ⋙ cX.model.E) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cY.ordinary.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (pullComparison Λ' f).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.pullIso a f).symm
        (equivalence Λ' X).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ cX.ordinary ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullComparison Λ f) _ ≪≫
      Functor.associator _ _ _
  let W := (Functor.whiskeringLeft (Modules Λ Y) (modules Λ Y) (modules Λ' X)).obj
    (equivalence Λ Y).functor
  refine ⟨W.preimageIso d, ?_⟩
  intro M
  have h := congrArg (fun t ↦ t.app M) (W.map_preimage d.hom)
  change (W.preimageIso d).hom.app ((equivalence Λ Y).functor.obj M) = d.hom.app M at h
  rw [h]
  simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  have hy := ((pullback Λ' f).mapIso (cY.ordinary.app M)).hom_inv_id
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hy
  rw [← Category.assoc ((pullback Λ' f).map (cY.ordinary.hom.app M))
    ((pullback Λ' f).map (cY.ordinary.inv.app M)), hy, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
