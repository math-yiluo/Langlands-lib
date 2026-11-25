/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
public import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationCoefficientLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Ordinary coefficient comparison for normalized rational realization

## References

* Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
* Bhatt--Scholze, Proposition 6.8.14(2)
* Bhatt--Scholze, Proposition 6.8.14(2), pp. 61--62
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The standard localization action, with the scheme module abbreviation in its type.
This is the existing constant-section action, with no change of scalar structure. -/
@[instance_reducible]
def rationalLocalizationModulesLinear (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (a : A →+* RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    Linear (Localization.Away t) (pbcModules Y
      (ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t))) :=
  scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
    (ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t))
    (scalarLocalizationCoefficientMapOfUniverses A B a t)

attribute [local irreducible] pbcIntegralDatum pbcRationalCoefficientEquiv
  ringedLocalizationRingOfUniverses ringedLocalizationRingUnitOfUniverses

private def ordinaryCoefficientEquivalence {Y : Scheme.{u}}
    {S T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : S ≅ T) :
    pbcModules Y S ≌ pbcModules Y T := by
  let d := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c.symm
  have : (CategoryTheory.Equivalence.refl (C := Y.ProEt)).functor.IsContinuous
      (ProEt.topology Y) (ProEt.topology Y) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 Y.ProEt) _ _)
  have : (CategoryTheory.Equivalence.refl (C := Y.ProEt)).inverse.IsContinuous
      (ProEt.topology Y) (ProEt.topology Y) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 Y.ProEt) _ _)
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl (C := Y.ProEt)) d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Y.ProEtᵒᵖ))
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj =
            d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Y.ProEtᵒᵖ))
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj T).obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫ 𝟙 _ = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)

private def ordinaryExtensionIdentification {Y : Scheme.{u}}
    {B S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (β : B ⟶ S)
    (F : pbcModules Y B ⥤ pbcModules Y S)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRingsOfUniverses β M)
    (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHomOfUniverses β M f ≫ eqToHom (hF N).symm) :
    F ≅ pbcExtend β := by
  have ho (M : pbcModules Y B) :
      (pbcExtend β).obj M = SheafOfModules.changeOfRingsOfUniverses β M :=
    (pbcExtensionExistence β).choose_spec.choose M
  have hm {M N : pbcModules Y B} (f : M ⟶ N) :
      (pbcExtend β).map f = eqToHom (ho M) ≫
        SheafOfModules.changeOfRingsHomOfUniverses β M f ≫ eqToHom (ho N).symm :=
    (pbcExtensionExistence β).choose_spec.choose_spec.choose f
  exact NatIso.ofComponents
    (fun M ↦ eqToIso (hF M) ≪≫ (eqToIso (ho M)).symm) (by
      intro M N f
      simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv]
      rw [hmap, hm]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans])

private def ordinaryCoefficientTensorComparison {Y : Scheme.{u}}
    {B S T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (β : B ⟶ S) (c : S ≅ T) (ψ : B ⟶ T) (hc : β ≫ c.hom = ψ) :
    pbcExtend β ⋙ (ordinaryCoefficientEquivalence c).functor ≅ pbcExtend ψ := by
  let e := ordinaryCoefficientEquivalence c
  let hr : e.inverse ⋙ pbcRestrict β ≅ pbcRestrict ψ :=
    pbcRestrictComp β c.hom ψ hc
  let adj := ((pbcScalarAdjunction β).comp e.toAdjunction).ofNatIsoRight hr
  exact Adjunction.leftAdjointUniq adj (pbcScalarAdjunction ψ)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The ordinary coefficient presentation agrees with standard sheaf localization.
This assertion concerns module sheaves and ordinary tensor extension only. -/
theorem rationalRealizationOrdinaryLocalization (R : RationalModuleRealization l E X) :
    let B := pbcAdicCompletion X (pbcIntegralDatum l E)
    let a := pbcCompletedScalarSections X (pbcIntegralDatum l E)
    let t := pbcUniformizer l E
    let S := ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} B (a t)
    letI := R.moduleLinear
    (fun [_localizedLinear : Linear (Localization.Away t)
        (pbcModules X S)] ↦
      ∀ (F : pbcModules X B ⥤ pbcModules X S)
        (hF : ∀ M, F.obj M =
          SheafOfModules.changeOfRingsOfUniverses
            (ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t)) M)
        (_hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
          SheafOfModules.changeOfRingsHomOfUniverses
            (ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} B (a t)) M f ≫
            eqToHom (hF N).symm),
        ∃ (G : pbcModules X S ⥤ pbcModules X (rationalCoefficientSheaf l X E)),
          G.IsEquivalence ∧ G.Additive ∧
          (∀ {K L} (f : K ⟶ L) (r : Localization.Away t),
            G.map (r • f) = pbcRationalCoefficientEquiv l E r • G.map f) ∧
          Nonempty (F ⋙ G ≅ pbcExtend (R.integralIso.hom ≫ R.inclusion)))
      (_localizedLinear := rationalLocalizationModulesLinear X (PbcIntegralRing l E)
        B a t) := by
  classical
  let := R.moduleLinear
  let := rationalLocalizationModulesLinear X (PbcIntegralRing l E)
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcCompletedScalarSections X (pbcIntegralDatum l E)) (pbcUniformizer l E)
  dsimp only
  intro F hF hmap
  obtain ⟨c, hc, hs⟩ := rationalRealizationCoefficientLocalization l E X R
  let e := ordinaryCoefficientEquivalence c
  let G := e.functor
  have hG : G = pbcRestrict c.inv := rfl
  have : G.IsEquivalence := e.isEquivalence_functor
  have : G.Additive := by rw [hG]; infer_instance
  refine ⟨G, inferInstance, inferInstance, ?_, ?_⟩
  · intro K L f r
    ext U x
    change (r • f).val.app U x = _
    rw [R.scalar_normalization]
    change (scalarLocalizationCoefficientMapOfUniverses (PbcIntegralRing l E)
      (pbcAdicCompletion X (pbcIntegralDatum l E))
      (pbcCompletedScalarSections X (pbcIntegralDatum l E))
      (pbcUniformizer l E) r).val U • f.val.app U x = _
    exact congrArg (fun s ↦ s • f.val.app U x) (hs r U).symm
  · let β := ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u}
      (pbcAdicCompletion X (pbcIntegralDatum l E))
      (pbcCompletedScalarSections X (pbcIntegralDatum l E) (pbcUniformizer l E))
    let ψ := R.integralIso.hom ≫ R.inclusion
    let q := ordinaryExtensionIdentification β F hF hmap
    exact ⟨Functor.isoWhiskerRight q G ≪≫ ordinaryCoefficientTensorComparison β c ψ hc⟩

end AlgebraicGeometry.Scheme
