/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarLocalizationTensorComparisonOfUniverses
public import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-! # Fraction colimits with independent site universes

Source: Stacks Project, Algebra, Tag 00CM; Modules on Sites, Tags 03CY and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe uC vC u v w uD vD uT vT uB vB r a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite
open scoped ChangeOfRings
namespace CategoryTheory

private theorem scalar_localization_colimitAux {R : Type u} [CommRing R] (s : R) :
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))
    ∃ e : colimit D ≅ ModuleCat.of R (Localization.Away s),
      ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ m := by
  dsimp only
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit s R
  let e := IsLocalizedModule.iso (Submonoid.powers s)
    (Algebra.linearMap R (Localization.Away s))
  have he (a : R) (n : ℕ) :
      e (LocalizedModule.mk (S := Submonoid.powers s) a ⟨s ^ n, ⟨n, rfl⟩⟩) =
        algebraMap R _ a * IsLocalization.Away.invSelf s ^ n := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit
      (S := Localization.Away s) s n).mul_left_cancel
    calc
      _ = e ((s ^ n) • LocalizedModule.mk (S := Submonoid.powers s)
          a ⟨s ^ n, ⟨n, rfl⟩⟩) := by rw [map_smul, Algebra.smul_def, map_pow]
      _ = algebraMap R _ a := by
        rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s),
          LocalizedModule.mk_cancel]
        exact IsLocalizedModule.iso_mk_one _ _ a
      _ = _ := by rw [mul_left_comm, ← mul_pow,
        IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(κ.trans e).toModuleIso, ?_⟩
  intro n a
  change e (κ ((colimit.ι (Functor.ofSequence (X := fun _ : ℕ ↦
    ModuleCat.of R R) (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R s))) n) a)) = _
  rw [hκ, he]

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

private def regularScalarAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    End (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  .of ((SheafOfModules.unitHomEquiv _).symm ⟨s.val, s.property⟩)

private abbrev sectionValueAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private abbrev localizationInvAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationCarrierOfUniverses O s X :=
  IsLocalization.Away.invSelf (R := O.obj.obj X) (sectionValueAux O s X)

private theorem localization_map_invAux
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    ringedSectionLocalizationMapOfUniverses O s g
      (localizationInvAux O s X) =
        localizationInvAux O s Y := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (R := O.obj.obj Y) (S := ringedSectionLocalizationCarrierOfUniverses O s Y)
      (sectionValueAux O s Y)).mul_left_cancel
  have hc (a : O.obj.obj X) :
      ringedSectionLocalizationMapOfUniverses O s g (algebraMap _ _ a) =
        algebraMap _ _ (O.obj.map g a) := by
    exact IsLocalization.Away.lift_eq _ _ a
  calc
    _ = ringedSectionLocalizationMapOfUniverses O s g
        (algebraMap _ _ (sectionValueAux O s X) * localizationInvAux O s X) := by
      rw [map_mul, hc, show O.obj.map g (sectionValueAux O s X) =
          sectionValueAux O s Y from s.property g]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf (sectionValueAux O s Y)).symm

private def fractionMapAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    PresheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheafOfUniverses O s :=
  (ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ localizationInvAux O s X ^ n)
      (fun {_ _} g ↦ by
        change ringedSectionLocalizationMapOfUniverses O s g _ = _
        rw [map_pow, localization_map_invAux]))

private theorem fractionMap_applyAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (X : Cᵒᵖ) (a : O.obj.obj X) :
    (fractionMapAux O s n).app X a =
      algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X) a *
        localizationInvAux O s X ^ n := by
  change a • localizationInvAux O s X ^ n = _
  exact Algebra.smul_def a _

private theorem scalar_applyAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) (a : O.obj.obj X) :
    (regularScalarAux O s).asHom.val.app X a = a * sectionValueAux O s X := by
  change a • sectionValueAux O s X = _
  rfl

private theorem fractionMap_stepAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (regularScalarAux O s).asHom.val ≫ fractionMapAux O s (n + 1) = fractionMapAux O s n := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change O.obj.obj X at a
  change (fractionMapAux O s (n + 1)).app X ((regularScalarAux O s).asHom.val.app X a) =
    (fractionMapAux O s n).app X a
  rw [fractionMap_applyAux, scalar_applyAux, fractionMap_applyAux, map_mul, pow_succ]
  calc
    _ = (algebraMap _ _ a * localizationInvAux O s X ^ n) *
        (algebraMap _ _ (sectionValueAux O s X) * localizationInvAux O s X) := by ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private def localizationPresheafCoconeAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (regularScalarAux O s).asHom) ⋙ SheafOfModules.forget _) where
  pt := ringedSectionLocalizationPresheafOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ fractionMapAux O s n) (by
    intro n
    change ((SheafOfModules.forget _).map
      ((Functor.ofSequence (fun _ ↦ (regularScalarAux O s).asHom)).map _)) ≫ _ = _ ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact fractionMap_stepAux O s n)

private def localizationPresheafCoconeIsColimitAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationPresheafCoconeAux O s) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro X
  let R := O.obj.obj X
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R R)
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul R R (sectionValueAux O s X)))
  let c := (PresheafOfModules.evaluation _ X).mapCocone
    (localizationPresheafCoconeAux O s)
  let F := (Functor.ofSequence (fun _ ↦ (regularScalarAux O s).asHom) ⋙
    SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ X
  let t : D ⟶ F := NatTrans.ofSequence (fun _ ↦ 𝟙 (ModuleCat.of R R)) (by
    intro n
    simp only [F, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change O.obj.obj X at a
    change (sectionValueAux O s X) * a = (regularScalarAux O s).asHom.val.app X a
    rw [scalar_applyAux, mul_comm])
  let et : D ≅ F := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro i j f; exact t.naturality f)
  let e := Classical.choose (scalar_localization_colimitAux (sectionValueAux O s X))
  have he := Classical.choose_spec (scalar_localization_colimitAux (sectionValueAux O s X))
  change ∀ (m : ℕ) (a : R), e.hom ((colimit.ι D m) a) =
    algebraMap R (Localization.Away (sectionValueAux O s X)) a *
      IsLocalization.Away.invSelf (sectionValueAux O s X) ^ m at he
  clear_value e
  apply (IsColimit.precomposeHomEquiv et c).toFun
  apply IsColimit.ofIsoColimit (colimit.isColimit D)
  refine Cocone.ext e ?_
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  dsimp only [et, c, Cocone.precompose, localizationPresheafCoconeAux,
    Functor.mapCocone, NatIso.ofComponents, NatTrans.ofSequence] at *
  change e.hom ((colimit.ι D m) a) = (fractionMapAux O s m).app X a
  rw [he, fractionMap_applyAux]

private def localizationSheafMapAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    (fractionMapAux O s n ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app _)

private theorem localizationSheafMap_stepAux
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (regularScalarAux O s).asHom ≫ localizationSheafMapAux O s (n + 1) =
      localizationSheafMapAux O s n := by
  apply SheafOfModules.hom_ext
  change (regularScalarAux O s).asHom.val ≫ (fractionMapAux O s (n + 1) ≫ _) = _
  rw [← Category.assoc, fractionMap_stepAux]
  rfl

private def localizationSheafCoconeAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (fun _ ↦ (regularScalarAux O s).asHom)) where
  pt := ringedSectionLocalizationOfUniverses O s
  ι := NatTrans.ofSequence (fun n ↦ localizationSheafMapAux O s n) (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change (regularScalarAux O s).asHom ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact localizationSheafMap_stepAux O s n)

private def localizationSheafCoconeIsColimitAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsColimit (localizationSheafCoconeAux O s) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  let hc := localizationPresheafCoconeIsColimitAux O s
  clear_value hc
  let U := SheafOfModules.forget ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  refine { desc := fun t ↦ (adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))
           fac := ?_
           uniq := ?_ }
  · intro t n
    apply U.map_injective
    change (fractionMapAux O s n ≫ adj.unit.app _) ≫
      U.map ((adj.homEquiv _ _).symm (hc.desc (U.mapCocone t))) = _
    rw [Category.assoc]
    erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    exact hc.fac (U.mapCocone t) n
  · intro t m hm
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro n
    rw [hc.fac]
    change fractionMapAux O s n ≫ (adj.homEquiv _ _ m) = _
    rw [Adjunction.homEquiv_unit, ← Category.assoc]
    exact congrArg (fun f ↦ U.map f) (hm n)

private theorem localizationSheafMap_zeroAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    localizationSheafMapAux O s 0 = ringedSectionLocalizationUnitOfUniverses O s := by
  unfold localizationSheafMapAux ringedSectionLocalizationUnitOfUniverses
  congr 2

/-- The localization of the regular module is its multiplication colimit, with
zeroth leg the localization unit.
Source: Stacks Project, Algebra, Tag 00CM, and Modules on Sites, Tag 03CY.
(blueprint: lem-weil-pbc-scalar-localization-fraction-colimit-of-universes).

Proof: the nth fraction map sends r to r/t^n. The module-localization colimit
comparison proves the universal property sectionwise. Evaluation jointly reflects
presheaf-module colimits, so the fraction cocone is a presheaf colimit. For a sheaf
target, the sheafification adjunction extends its descent map uniquely; the unit
naturality and the presheaf colimit equations prove factorization and uniqueness.
The zeroth fraction map sends r to r/1, hence is the stated localization unit. -/
private theorem scalarLocalization_regularColimitAux
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
      (fun _ ↦ (SheafOfModules.unitHomEquiv _).symm ⟨s.val, s.property⟩)),
      Nonempty (IsColimit c) ∧ ∃ e : c.pt ≅ ringedSectionLocalizationOfUniverses O s,
        (show SheafOfModules.unit _ ⟶ c.pt from c.ι.app 0) ≫ e.hom =
          ringedSectionLocalizationUnitOfUniverses O s := by
  refine ⟨localizationSheafCoconeAux O s, ⟨localizationSheafCoconeIsColimitAux O s⟩,
    Iso.refl _, ?_⟩
  change localizationSheafMapAux O s 0 ≫ 𝟙 _ = _
  rw [Category.comp_id, localizationSheafMap_zeroAux]

end CategoryTheory

namespace CategoryTheory

attribute [local irreducible] scalarLocalizationCoefficientMapOfUniverses
  SheafOfModules.scalarTelescopeTensorUnitOfUniverses
    SheafOfModules.scalarTelescopeRegularTensorIsoOfUniverses
  SheafOfModules.tensorObjIsoSheafification
  ringedLocalizationRingOfUniverses ringedLocalizationRingUnitOfUniverses

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private theorem transport_scalar_colimitAux
    {B D : Type*} [Category B] [Category D]
    (X : B) (u : X ⟶ X) (Y : D) (v : Y ⟶ Y)
    (F : B ⥤ D) (e : F.obj X ≅ Y)
    (he : F.map u ≫ e.hom = e.hom ≫ v)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)))
    (hc : IsColimit c) [PreservesColimit
      (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)) F]
    {Z : D} (β : F.obj c.pt ≅ Z)
    (l : ℕ → (Y ⟶ Z)) (hl : ∀ n, v ≫ l (n + 1) = l n)
    (hz : F.map (c.ι.app 0) ≫ β.hom = e.hom ≫ l 0)
    (w : Z ⟶ Z) [Mono w]
    (hcenter : ∀ n, F.map u ≫ F.map (c.ι.app n) ≫ β.hom =
      F.map (c.ι.app n) ≫ β.hom ≫ w)
    (hcenterl : ∀ n, v ≫ l n = l n ≫ w) :
    ∃ d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ v)),
      Nonempty (IsColimit d) ∧ ∃ γ : d.pt ≅ Z,
        ∀ n, d.ι.app n ≫ γ.hom = l n := by
  let S := Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ v)
  let τ : S ⋙ F ⟶ T := NatTrans.ofSequence (fun _ ↦ e.hom) (by
    intro n
    simpa only [S, T, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] using he)
  let ε : S ⋙ F ≅ T := NatIso.ofComponents (fun _ ↦ e) (by
    intro n m f
    exact τ.naturality f)
  let d := (Cocone.precompose ε.inv).obj (F.mapCocone c)
  have hd : IsColimit d :=
    (IsColimit.precomposeHomEquiv ε.symm (F.mapCocone c)).symm
      (isColimitOfPreserves F hc)
  refine ⟨d, ⟨hd⟩, β, ?_⟩
  have h (n : ℕ) : F.map (c.ι.app n) ≫ β.hom = e.hom ≫ l n := by
    induction n with
    | zero => exact hz
    | succ n ih =>
      apply (cancel_mono w).1
      have hw := c.w (homOfLE (Nat.le_succ n))
      simp only [Functor.ofSequence_map_homOfLE_succ] at hw
      calc
        (F.map (c.ι.app (n + 1)) ≫ β.hom) ≫ w =
            F.map u ≫ F.map (c.ι.app (n + 1)) ≫ β.hom := by
          rw [Category.assoc, hcenter]
        _ = F.map (c.ι.app n) ≫ β.hom := by rw [← F.map_comp_assoc, hw]
        _ = e.hom ≫ l n := ih
        _ = (e.hom ≫ l (n + 1)) ≫ w := by
          rw [Category.assoc, ← hcenterl, ← hl n]
  intro n
  change (e.inv ≫ F.map (c.ι.app n)) ≫ β.hom = _
  rw [Category.assoc, h n]
  simp only [Iso.inv_hom_id_assoc]

private theorem regular_tensor_scalar_applyAux
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (f : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) (r : R.obj.obj V)
    (hf : f.val.app V (1 : R.obj.obj V) = r) :
    letI := SheafOfModules.cochainModulesMonoidal R
    ∀ (e : (tensorRight M).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅ M),
      (∀ y : M.val.obj V, e.inv.val.app V y =
        (SheafOfModules.scalarTelescopeTensorUnitOfUniverses
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M
        ).app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] y)) →
      e.hom.val.app V (((tensorRight M).map f).val.app V (e.inv.val.app V x)) = r • x := by
  let := SheafOfModules.cochainModulesMonoidal R
  dsimp only
  intro e he
  let X := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  have hn := SheafOfModules.scalarTelescopeTensorUnit_naturalityOfUniverses f M
  have hn' := congrArg (fun g ↦ g.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
  have hnorm := congrArg (((tensorRight M).map f).val.app V) (he x)
  have ht : ((f.val ▷ M.val).app V) ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) =
      r • ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
    change (f.val.app V (1 : R.obj.obj V)) ⊗ₜ[R.obj.obj V] x = _
    rw [hf]
    exact ((TensorProduct.smul_tmul' r (1 : R.obj.obj V) x).trans
      (congrArg (fun y : R.obj.obj V ↦ y ⊗ₜ[R.obj.obj V] x) (mul_one r))).symm
  have hp := congrArg ((SheafOfModules.scalarTelescopeTensorUnitOfUniverses X M).app V) ht
  have hs := ((SheafOfModules.scalarTelescopeTensorUnitOfUniverses X M).app V).hom.map_smul
    r ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)
  have hnall := hnorm.trans (hn'.trans (hp.trans hs))
  have hmap := congrArg (e.hom.val.app V) hnall
  have he' := (e.hom.val.app V).hom.map_smul r
    ((SheafOfModules.scalarTelescopeTensorUnitOfUniverses X M).app V
      ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x))
  have hi := congrArg (fun g ↦ g.val.app V x) e.inv_hom_id
  change e.hom.val.app V (e.inv.val.app V x) = x at hi
  have hh := congrArg (fun y ↦ r • e.hom.val.app V y) (he x).symm
  exact hmap.trans (he'.trans (hh.trans (congrArg (fun y ↦ r • y) hi)))

private theorem isIso_scalar_of_inverseAux
    {B : Type*} [Category B] [Preadditive B]
    {T : Type*} [CommRing T] [Linear T B]
    (X : B) (r s : T) (h : r * s = 1) : IsIso (r • 𝟙 X) := by
  refine ⟨⟨s • 𝟙 X, ?_, ?_⟩⟩
  · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [mul_comm s r, h, one_smul]
  · simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [h, one_smul]

private theorem inverse_scalar_legs_stepAux
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A B] [Linear S D]
    (U : D ⥤ B) (X : B) (Y : D) (η : X ⟶ U.obj Y)
    (t : A) (r s : S) (hrs : r * s = 1)
    (hz : t • 𝟙 (U.obj Y) = U.map (r • 𝟙 Y)) (n : ℕ) :
    (t • 𝟙 X) ≫ (η ≫ U.map (s ^ (n + 1) • 𝟙 Y)) =
      η ≫ U.map (s ^ n • 𝟙 Y) := by
  rw [Linear.smul_comp, Category.id_comp, ← Linear.comp_smul]
  rw [← Category.id_comp (U.map (s ^ (n + 1) • 𝟙 Y)), ← Linear.smul_comp, hz,
    ← U.map_comp]
  apply congrArg (fun f ↦ η ≫ U.map f)
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
  congr 1
  calc
    s ^ (n + 1) * r = s ^ n * (r * s) := by ring
    _ = s ^ n := by rw [hrs, mul_one]

private theorem tensor_scalar_colimitAux
    {B D T : Type*} [Category B] [Category D] [Category T]
    [Preadditive D] [Preadditive T]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A D] [Linear S T]
    (X : B) (u : X ⟶ X) (Y : D) (F : B ⥤ D) (e : F.obj X ≅ Y)
    (t : A) (he : F.map u ≫ e.hom = e.hom ≫ (t • 𝟙 Y))
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)))
    (hc : IsColimit c) [PreservesColimit
      (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ u)) F]
    (U : T ⥤ D) (N : T) (η : Y ⟶ U.obj N) (β : F.obj c.pt ≅ U.obj N)
    (hzero : F.map (c.ι.app 0) ≫ β.hom = e.hom ≫ η)
    (r s : S) (hrs : r * s = 1) (hz : t • 𝟙 (U.obj N) = U.map (r • 𝟙 N)) :
    ∃ d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ t • 𝟙 Y)),
      Nonempty (IsColimit d) ∧ ∃ γ : d.pt ≅ U.obj N,
        ∀ n : ℕ, d.ι.app n ≫ γ.hom = η ≫ U.map (s ^ n • 𝟙 N) := by
  have hu : F.map u = t • 𝟙 (F.obj X) := by
    apply (cancel_mono e.hom).1
    rw [he, Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp]
  have : IsIso (r • 𝟙 N) := isIso_scalar_of_inverseAux N r s hrs
  have : IsIso (t • 𝟙 (U.obj N)) := by rw [hz]; infer_instance
  refine transport_scalar_colimitAux X u Y (t • 𝟙 Y) F e he c hc β
    (fun n ↦ η ≫ U.map (s ^ n • 𝟙 N))
    (inverse_scalar_legs_stepAux U Y N η t r s hrs hz) ?_ (t • 𝟙 (U.obj N)) ?_ ?_
  · simpa only [pow_zero, one_smul, Functor.map_id, Category.comp_id] using hzero
  · intro n
    rw [hu]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

set_option linter.style.whitespace false in
-- The sectionwise tensor normalization has a large elaborated type.
/-- The fraction legs exhibit restricted scalar extension as the module-sheaf colimit.
Source: Stacks Project, algebra.tex Tag 00CM; sites-modules.tex Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-fraction-colimit-of-universes).

Proof: the sectionwise fraction maps from R into R[1/t] give a colimit: a
compatible family sends r/t^n to the stage-n image of r. The fraction equality
criterion gives equality at a common stage, including t-torsion. These maps
commute with restrictions and descend through module sheafification. Tensoring
with M preserves this colimit by tensor--Hom adjunction. The comparison between
restricted extension of scalars and the sheaf tensor identifies the resulting
object with U(N); the normalized unit fixes the zeroth leg, and multiplication
by the inverse powers of t fixes all the other legs. -/
private theorem scalarLocalization_moduleColimitAux
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (ringedLocalizationRingOfUniverses R (a t))))
    (hN : N = SheafOfModules.changeOfRingsOfUniverses (ringedLocalizationRingUnitOfUniverses R (a
      t)) M)
    (U : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU : U = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnitOfUniverses R (a t))))
    (η : M ⟶ U.obj N)
    (hη : scalarLocalizationUnitSectionsOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t))
      M N hN (η ≫ eqToHom (congrArg (fun T ↦ T.obj N) hU))) :
    (fun [_source : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_target : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R (a t))))] ↦
      ∃ c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ M) (fun _n ↦ t • 𝟙 M)),
        Nonempty (IsColimit c) ∧ ∃ β : c.pt ≅ U.obj N,
          ∀ n : ℕ, c.ι.app n ≫ β.hom = η ≫ U.map
            (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 N))
      (_source := scalarLocalizationCoefficientLinearOfUniverses A R a)
      (_target := scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
        (ringedLocalizationRingOfUniverses R (a t)) (scalarLocalizationCoefficientMapOfUniverses A
          R a t)) := by
  classical
  generalize hs : scalarLocalizationCoefficientLinearOfUniverses A R a = src
  generalize ht : scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
    (ringedLocalizationRingOfUniverses R (a t)) (scalarLocalizationCoefficientMapOfUniverses A R a
      t) = tgt
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : HasWeakSheafify J AddCommGrpCat.{u} := inferInstance
  subst U
  subst N
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let S := ringedLocalizationRingOfUniverses R (a t)
  let φ := ringedLocalizationRingUnitOfUniverses R (a t)
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  obtain ⟨eT, heT⟩ := SheafOfModules.exists_scalarTelescopeTensorComparisonOfUniverses φ M
  let : Linear A (SheafOfModules O) := src
  let : Linear (Localization.Away t) (SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
    tgt
  let := SheafOfModules.cochainModulesMonoidal R
  let := SheafOfModules.cochainModulesSymmetric R
  let X := SheafOfModules.unit O
  let F := tensorRight M
  let ε : F.obj X ≅ M := SheafOfModules.scalarTelescopeRegularTensorIsoOfUniverses M
  have hεinv (V : Cᵒᵖ) (x : M.val.obj V) : ε.inv.val.app V x =
      (SheafOfModules.scalarTelescopeTensorUnitOfUniverses X M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) :=
    SheafOfModules.scalarTelescopeRegularTensorIso_inv_applyOfUniverses M V x
  clear_value ε
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := scalarLocalization_regularColimitAux R (a t)
  obtain ⟨eS, heS⟩ := ringedLocalizationRing_moduleComparisonOfUniverses R (a t)
  let β : F.obj c.pt ≅ U.obj (SheafOfModules.changeOfRingsOfUniverses.{vC, uC, u, u} φ M) :=
    F.mapIso ec ≪≫ F.mapIso eS.symm ≪≫ eT
  have : PreservesColimitsOfSize.{0, 0} F := by
    exact SheafOfModules.cochainTensorRightPreservesColimits R M
  have hh : F.map (c.ι.app 0) ≫ β.hom =
      F.map (c.ι.app 0 ≫ ec.hom ≫ eS.inv) ≫ eT.hom := by
    simp only [β, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp, Category.assoc]
  clear_value β
  have hbase (V : Cᵒᵖ) :
      (c.ι.app 0 ≫ ec.hom ≫ eS.inv).val.app V (1 : R.obj.obj V) =
        (1 : S.obj.obj V) := by
    rw [← Category.assoc, hec]
    have : IsIso eS.hom.val := (SheafOfModules.forget _).map_isIso eS.hom
    apply (ModuleCat.mono_iff_injective (eS.hom.val.app V)).1 inferInstance
    have h := heS V (1 : ringedSectionLocalizationCarrierOfUniverses R (a t) V)
    have hi := congrArg (fun f ↦ f.val.app V
      ((ringedSectionLocalizationUnitOfUniverses R (a t)).val.app V (1 : R.obj.obj V)))
        eS.inv_hom_id
    change (eS.hom.val.app V)
      ((eS.inv.val.app V)
        ((ringedSectionLocalizationUnitOfUniverses R (a t)).val.app V (1 : R.obj.obj V))) =
      (ringedSectionLocalizationUnitOfUniverses R (a t)).val.app V (1 : R.obj.obj V) at hi
    apply hi.trans
    change ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
      (ringedSectionLocalizationPresheafOfUniverses R (a t))).app V
        ((1 : R.obj.obj V) • (1 : ringedSectionLocalizationCarrierOfUniverses R (a t) V)) = _
    rw [one_smul]
    simp only [map_one] at h
    convert h.symm using 1 <;> (with_unfolding_all rfl)
  have hzero : F.map (c.ι.app 0) ≫ β.hom = ε.hom ≫ η := by
    apply (cancel_epi ε.inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (F.map (c.ι.app 0) ≫ β.hom).val.app V (ε.inv.val.app V x) = η.val.app V x
    have hhi := congrArg (fun f ↦ f.val.app V (ε.inv.val.app V x)) hh
    apply hhi.trans
    have hn := SheafOfModules.scalarTelescopeTensorUnit_naturalityOfUniverses
      (c.ι.app 0 ≫ ec.hom ≫ eS.inv) M
    have hn' := congrArg (fun f ↦ f.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) hn
    have hb := congrArg (fun y ↦
      (SheafOfModules.scalarTelescopeTensorUnitOfUniverses _ M).app V (y ⊗ₜ[R.obj.obj V] x)) (hbase
        V)
    have hnorm := congrArg ((F.map (c.ι.app 0 ≫ ec.hom ≫ eS.inv)).val.app V)
      (hεinv V x)
    exact (congrArg (eT.hom.val.app V) (hnorm.trans (hn'.trans hb))).trans
      ((heT V 1 x).trans (by
        simpa only [eqToHom_refl, Functor.map_id, Category.comp_id] using (hη V x).symm))
  have hscalar : F.map ((SheafOfModules.unitHomEquiv X).symm
      ⟨(a t).val, (a t).property⟩) ≫ ε.hom = ε.hom ≫ (t • 𝟙 M) := by
    apply (cancel_epi ε.inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    subst src
    change ε.hom.val.app V
      ((F.map ((SheafOfModules.unitHomEquiv X).symm
        ⟨(a t).val, (a t).property⟩)).val.app V (ε.inv.val.app V x)) = (a t).val V • x
    exact regular_tensor_scalar_applyAux R M _ V x ((a t).val V) (by
      exact one_smul ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) _) ε (hεinv V)
  let Z := U.obj (SheafOfModules.changeOfRingsOfUniverses.{vC, uC, u, u} φ M)
  let z : Z ⟶ Z := t • 𝟙 Z
  have hz : z = U.map ((algebraMap A (Localization.Away t) t) •
      𝟙 (SheafOfModules.changeOfRingsOfUniverses.{vC, uC, u, u} φ M)) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    subst src
    subst tgt
    change (a t).val V • x =
      (scalarLocalizationCoefficientMapOfUniverses A R a t
        (algebraMap A (Localization.Away t) t)).val V •
          (show (SheafOfModules.changeOfRingsOfUniverses φ M).val.obj V from x)
    have hb : scalarLocalizationCoefficientMapOfUniverses A R a t
        (algebraMap A (Localization.Away t) t) =
        scalarLocalizationSectionsMapOfUniverses φ (a t) :=
      by
        unfold scalarLocalizationCoefficientMapOfUniverses
        exact IsLocalization.Away.lift_eq (S := Localization.Away t) t
          (scalarLocalizationSections_isUnitOfUniverses A R a t) t
    exact (congrArg (fun b ↦ b.val V •
      (show (SheafOfModules.changeOfRingsOfUniverses φ M).val.obj V from x)) hb).symm
  exact tensor_scalar_colimitAux X _ M F ε t hscalar c hc U _ η β hzero
    (algebraMap A (Localization.Away t) t)
    (IsLocalization.Away.invSelf t : Localization.Away t)
    (IsLocalization.Away.mul_invSelf t) hz

end CategoryTheory

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option linter.style.whitespace false in
/-- The ordinary sequential colimit of a scalar sequence of complexes.
Source: Stacks Project, algebra.tex, Tag 00CM; sites-modules.tex, Tags 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-fraction-colimit-of-universes).

Proof: on each object V and degree i, send the stage-n element x to t^(-n) tensor x.
For any compatible family, send a fraction x/t^n to the stage-n image of x.
If two fractions agree, a power of t kills their cross difference; passing to the
common stage n+m+k makes their images equal. This proves well-definedness even
with t-torsion. Common stages prove additivity and linearity; all fractions prove
uniqueness. These maps commute with restriction. Module sheafification gives the
universal property for sheaf modules, and tensor--Hom adjunction extends it from
R to every module. Apply it degreewise. The maps commute with differentials by
linearity, as do their inverses. Thus the termwise restricted scalar extension is
isomorphic to the sequential colimit complex. The displayed normalization is the
fraction formula, using the section normalization of the zeroth leg. -/
theorem scalarLocalization_complexColimitOfUniverses
    (A : Type v) [CommRing A]
    (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))]
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))
    (hE : ∀ M, E.obj M =
      SheafOfModules.changeOfRingsOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t)) M)
    (_hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hE M) ≫
      SheafOfModules.changeOfRingsHomOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t)) M
        f ≫
        eqToHom (hE N).symm)
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hU₀ : U₀ = SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map
        (ringedLocalizationRingUnitOfUniverses R (a t))))
    [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      K ⟶ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (unitSections : ∀ (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (i : ℤ),
      scalarLocalizationUnitSectionsOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t))
        (K.X i) (E.obj (K.X i)) (hE (K.X i))
        ((unitComplex K).f i ≫
          eqToHom (congrArg (fun T ↦ T.obj (E.obj (K.X i))) hU₀)))
 :
    (fun [_source : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_target : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R (a t))))] ↦
      ∀ (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      ∃ (c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K))),
        Nonempty (IsColimit c) ∧
        ∃ β : c.pt ≅ (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
          ∀ n : ℕ, (show K ⟶ c.pt from c.ι.app n) ≫ β.hom = (unitComplex K) ≫
            (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
                𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
      (_source := scalarLocalizationCoefficientLinearOfUniverses A R a)
      (_target := scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
        (ringedLocalizationRingOfUniverses R (a t)) (scalarLocalizationCoefficientMapOfUniverses A
          R a t))   := by
  let B := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let B' := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
    (ringedLocalizationRingOfUniverses R (a t)))
  let : Linear A B := scalarLocalizationCoefficientLinearOfUniverses A R a
  let : Linear (Localization.Away t) B' :=
    scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
      (ringedLocalizationRingOfUniverses R (a t)) (scalarLocalizationCoefficientMapOfUniverses A R
        a t)
  dsimp only
  intro K
  let T := (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let l (n : ℕ) : K ⟶ T := unitComplex K ≫
    (U₀.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
        𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  have hdegree (i : ℤ) := scalarLocalization_moduleColimitAux A R a t
    (K.X i) (E.obj (K.X i)) (hE (K.X i)) U₀ hU₀
    ((unitComplex K).f i) (unitSections K i)
  have hstep (n : ℕ) : (t • 𝟙 K) ≫ l (n + 1) = l n := by
    apply HomologicalComplex.hom_ext
    intro i
    obtain ⟨c, ⟨hc⟩, β, hβ⟩ := hdegree i
    change (t • 𝟙 (K.X i)) ≫ (l (n + 1)).f i = (l n).f i
    change (t • 𝟙 (K.X i)) ≫ ((unitComplex K).f i ≫ U₀.map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ (n + 1)) •
        𝟙 (E.obj (K.X i)))) = _
    rw [← hβ (n + 1)]
    change (t • 𝟙 (K.X i)) ≫ (c.ι.app (n + 1) ≫ β.hom) =
      (unitComplex K).f i ≫ U₀.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (E.obj (K.X i)))
    rw [← hβ n, ← Category.assoc]
    congr 1
    simpa only [Functor.ofSequence_map_homOfLE_succ] using
      c.w (homOfLE (Nat.le_succ n))
  let c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)) :=
    { pt := T
      ι := NatTrans.ofSequence l (by
        intro n
        rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        change (t • 𝟙 K) ≫ l (n + 1) = l n ≫ 𝟙 T
        rw [Category.comp_id]
        exact hstep n) }
  refine ⟨c, ?_, Iso.refl T, ?_⟩
  · suffices h : ∀ i : ℤ, Nonempty (IsColimit
        ((HomologicalComplex.eval B (.up ℤ) i).mapCocone c)) by
      exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i ↦ Classical.choice (h i))⟩
    intro i
    obtain ⟨d, ⟨hd⟩, β, hβ⟩ := hdegree i
    let V := HomologicalComplex.eval B (.up ℤ) i
    let S := Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)
    let D := Functor.ofSequence (X := fun _n : ℕ ↦ K.X i)
      (fun _n ↦ t • 𝟙 (K.X i))
    let τ : D ⟶ S ⋙ V := NatTrans.ofSequence (fun _n ↦ 𝟙 (K.X i)) (by
      intro n
      simp only [D, S, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      change (t • 𝟙 (K.X i)) ≫ 𝟙 _ = 𝟙 _ ≫ (t • 𝟙 (K.X i))
      simp only [Category.comp_id, Category.id_comp])
    let e : D ≅ S ⋙ V := NatIso.ofComponents (fun _n ↦ Iso.refl _) (by
      intro n m f
      exact τ.naturality f)
    apply Nonempty.intro
    apply (IsColimit.precomposeHomEquiv e (V.mapCocone c)).toFun
    apply IsColimit.ofIsoColimit hd
    refine Cocone.ext β ?_
    intro n
    change d.ι.app n ≫ β.hom = (𝟙 (K.X i)) ≫ (l n).f i
    rw [Category.id_comp]
    exact hβ n
  · intro n
    exact Category.comp_id _

end CategoryTheory
