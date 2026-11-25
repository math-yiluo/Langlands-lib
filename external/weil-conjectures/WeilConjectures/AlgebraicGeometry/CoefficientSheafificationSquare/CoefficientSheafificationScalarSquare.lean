/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationMapForget
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-! # A normalized scalar square for finite coefficient presentations

Compose scalar restriction on module presheaves with the sheafification square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
section CoefficientSquare
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B B' R S : Type (u + 1)} [CommRing B] [CommRing B'] [CommRing R] [CommRing S]
    (q : B →+* B') (b : R →+* B) (b' : S →+* B') (r : R →+* S)
    (h : b'.comp r = q.comp b)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)

abbrev coefficientPresheaf {K L : Type (u + 1)} [CommRing K] [CommRing L]
    (c : K →+* L) :=
  sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} c) ⋙
    sheafToPresheaf J (ModuleCat.{u + 1} K) ⋙ ProEtale.finiteCoefficientModulePresheaf C K

include h in
@[irreducible] def coefficientPresheafIso :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        coefficientPresheaf J b ≅ coefficientPresheaf J b' ⋙ rawRestriction r :=
  NatIso.ofComponents (fun F ↦ PresheafOfModules.isoMk
    (fun V ↦ (ModuleCat.restrictScalarsComp'App b q (q.comp b) rfl (F.obj.obj V)).symm ≪≫
      ModuleCat.restrictScalarsComp'App r b' (q.comp b) h.symm (F.obj.obj V))
    (by intros; ext x; rfl)) (by intros; ext V x; rfl)

omit [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
theorem coefficientPresheafIso_forget (F : Sheaf J (ModuleCat.{u + 1} B')) :
    (PresheafOfModules.toPresheaf _).map
      ((coefficientPresheafIso J q b b' r h).hom.app F) = 𝟙 _ := by
  unfold coefficientPresheafIso
  ext V x
  rfl

abbrev coefficientRealization {K : Type (u + 1)} [CommRing K]
    {V : Sheaf J RingCat.{u + 1}}
    (γ : (Functor.const Cᵒᵖ).obj (RingCat.of K) ⟶ V.obj)
    [Presheaf.IsLocallyInjective J γ] [Presheaf.IsLocallySurjective J γ] :=
  sheafToPresheaf J (ModuleCat.{u + 1} K) ⋙
    ProEtale.finiteCoefficientModulePresheaf C K ⋙ PresheafOfModules.sheafification γ

include h ha in
@[irreducible] def coefficientScalarIso :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} b) ⋙
          coefficientRealization J α) ≅
      (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} b') ⋙
        coefficientRealization J β) ⋙ SheafOfModules.restrictScalars a :=
  Functor.isoWhiskerRight (coefficientPresheafIso J q b b' r h)
      (PresheafOfModules.sheafification α) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coefficientPresheaf J b') (rawIso J r a α β ha) ≪≫
    (Functor.associator _ _ _).symm

theorem coefficientScalarIso_forget (F : Sheaf J (ModuleCat.{u + 1} B')) :
    (SheafOfModules.toSheaf T).map
      ((coefficientScalarIso (J := J) (q := q) (b := b) (b' := b')
        (r := r) (h := h) (a := a) (α := α) (β := β) (ha := ha)).hom.app F) = 𝟙 _ := by
  unfold coefficientScalarIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp]
  rw [← Functor.map_comp, rawIso_map_forget]
  rw [coefficientPresheafIso_forget]
  exact (presheafToSheaf J AddCommGrpCat.{u + 1}).map_id _

end CoefficientSquare
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
