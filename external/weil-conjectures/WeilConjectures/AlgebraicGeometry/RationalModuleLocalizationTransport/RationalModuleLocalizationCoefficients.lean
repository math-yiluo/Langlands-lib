/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact

/-! # Normalized coefficients and exact extension for rational module localization

## References

* Bhatt--Scholze, Lemma 6.8.2 and the construction of Proposition 6.8.14(2)
* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace RationalModuleLocalizationTransport

section

/-- Normalized coefficient helper for completed-to-rational extension. -/
def rationalSections (X : Scheme.{u}) :
    E →+* RingCat.sectionsSubring
      ((rationalCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun U ↦ ContinuousMap.const U.unop.left (ULift.up a),
        fun _ ↦ rfl⟩
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl
      map_zero' := by ext; rfl
      map_add' := by intros; ext; rfl }

/-- Normalized coefficient helper for completed-to-rational extension. -/
@[instance_reducible]
def rationalLinear (X : Scheme.{u}) :
    Linear E (pbcModules X (rationalCoefficientSheaf l X E)) :=
  scalarLocalizationCoefficientLinearOfUniverses E
    (rationalCoefficientSheaf l X E) (rationalSections l E X)

private def extensionComp {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend c :=
  (((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).ofNatIsoRight
    (pbcRestrictComp a b c h)).leftAdjointUniq (pbcScalarAdjunction c)

private theorem extensionIsoExact {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (e : R ≅ S) :
    PreservesFiniteLimits (pbcExtend e.hom) ∧
      PreservesFiniteColimits (pbcExtend e.hom) := by
  let T := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso e)
  let j : pbcExtend e.hom ≅ pbcRestrict e.inv :=
    (pbcScalarAdjunction e.hom).leftAdjointUniq T.symm.toAdjunction
  exact ⟨preservesFiniteLimits_of_natIso j.symm,
    preservesFiniteColimits_of_natIso j.symm⟩

private def integralSections (X : Scheme.{u}) :
    PbcIntegralRing l E →+* RingCat.sectionsSubring
      ((integralCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun U ↦ ContinuousMap.const U.unop.left a, fun _ ↦ rfl⟩
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl
      map_zero' := by ext; rfl
      map_add' := by intros; ext; rfl }

private theorem coeffRingSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private theorem coeffAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} X

private theorem coeffAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

attribute [local instance] coeffRingSheafify coeffAbSheafify coeffAbLocallyBijective

private def integralLocalizationPresentation (X : Scheme.{u}) :
    ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (integralCoefficientSheaf l X E)
      (integralSections.{u} l E X (pbcUniformizer.{u} l E)) ≅
        integralCoefficientLocalization l X E := by
  letI := coefficientExtensionNormedField l E
  let q : ringedLocalizationRingPresheafOfUniverses.{u + 1, u + 1, u}
      (integralCoefficientSheaf l X E)
      (integralSections.{u} l E X (pbcUniformizer.{u} l E)) ≅
        localizedContinuousMapPresheaf X (PbcIntegralRing l E) (pbcUniformizer l E) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V g
      apply CommRingCat.hom_ext
      change localizedContinuousMapRestriction X (PbcIntegralRing l E)
        (pbcUniformizer l E) g = ringedSectionLocalizationMapOfUniverses
          (integralCoefficientSheaf l X E)
          (integralSections.{u} l E X (pbcUniformizer.{u} l E)) g
      apply IsLocalization.ringHom_ext
        (Submonoid.powers (ContinuousMap.const U.unop.left (pbcUniformizer l E)))
      ext x
      simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
        ringedSectionLocalizationMapOfUniverses]
      rfl)
  exact (presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso q

private theorem integralExtensionExact (X : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (integralRationalCoefficientMap l E X)) ∧
      PreservesFiniteColimits (pbcExtend (integralRationalCoefficientMap l E X)) := by
  letI := coefficientExtensionNormedField l E
  let R := integralCoefficientSheaf l X E
  let s := integralSections l E X (pbcUniformizer l E)
  let j := integralLocalizationPresentation l E X
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  let e := j ≪≫ b
  let a := ringedLocalizationRingUnitOfUniverses R s
  have he : a ≫ e.hom = integralRationalCoefficientMap l E X := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    change ((show C(U.unop.left, ULift.{u + 1, u} E) from
      (b.hom.hom.app U) ((j.hom.hom.app U) ((a.hom.app U) z))) x).down = _
    have hj : (a ≫ j.hom).hom =
        { app := fun U ↦ CommRingCat.ofHom
            (((toSheafify (ProEt.topology X)
              (localizedContinuousMapPresheaf X (PbcIntegralRing l E)
                (pbcUniformizer l E))).app U).hom.comp
                (algebraMap C(U.unop.left, PbcIntegralRing l E)
                  (Localization.Away (ContinuousMap.const U.unop.left
                    (pbcUniformizer l E)))))
          naturality := by
            intro U V g
            apply CommRingCat.hom_ext
            ext z
            simp only [CommRingCat.hom_comp, RingHom.comp_apply]
            have hn := ConcreteCategory.congr_hom
              ((toSheafify (ProEt.topology X)
                (localizedContinuousMapPresheaf X (PbcIntegralRing l E)
                  (pbcUniformizer l E))).naturality g)
                (algebraMap C(U.unop.left, PbcIntegralRing l E)
                  (Localization.Away (ContinuousMap.const U.unop.left
                    (pbcUniformizer l E))) z)
            change ((toSheafify (ProEt.topology X)
              (localizedContinuousMapPresheaf X (PbcIntegralRing l E)
                (pbcUniformizer l E))).app V).hom
                (localizedContinuousMapRestriction X (PbcIntegralRing l E)
                  (pbcUniformizer l E) g
                    (algebraMap C(U.unop.left, PbcIntegralRing l E)
                      (Localization.Away (ContinuousMap.const U.unop.left
                        (pbcUniformizer l E))) z)) = _ at hn
            simpa only [localizedContinuousMapRestriction, IsLocalization.Away.map,
              IsLocalization.map_eq, R, integralCoefficientSheaf,
              integralCoefficientLocalization, localizedContinuousCoefficientSheaf,
              CommRingCat.hom_comp, RingHom.comp_apply] using! hn } := by
      unfold a j integralLocalizationPresentation
      dsimp only [ringedLocalizationRingUnitOfUniverses, Iso.trans_hom]
      change ringedLocalizationRingPresheafUnitOfUniverses R s ≫
        toSheafify (ProEt.topology X) _ ≫ sheafifyMap (ProEt.topology X) _ = _
      rw [← toSheafify_naturality]
      rfl
    have hjU := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app U) hj) z
    change j.hom.hom.app U (a.hom.app U z) = _ at hjU
    rw [hjU]
    exact hb U z x
  obtain ⟨F, hobj, hmap, _, hlim, hcolim, hF⟩ :=
    scalarLocalization_sheaf_exact (ProEt.topology X) R s
  have hEF : pbcExtend a = F := by
    refine CategoryTheory.Functor.ext (F := pbcExtend a) (G := F)
      (fun M ↦ (reductionChange_obj_eq X a M).trans (hobj M).symm) ?_
    intro M N f
    simp only [reductionChange_map_eq, hmap, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans]
    rfl
  have hlimA : PreservesFiniteLimits (pbcExtend a) := by rw [hEF]; exact hlim
  have hcolimA : PreservesFiniteColimits (pbcExtend a) := by rw [hEF]; exact hcolim
  have := (extensionIsoExact e).1
  have := (extensionIsoExact e).2
  have : PreservesFiniteLimits (pbcExtend a ⋙ pbcExtend e.hom) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (pbcExtend a ⋙ pbcExtend e.hom) :=
    comp_preservesFiniteColimits _ _
  exact ⟨preservesFiniteLimits_of_natIso (extensionComp a e.hom _ he),
    preservesFiniteColimits_of_natIso (extensionComp a e.hom _ he)⟩

/-- Normalized coefficient helper for completed-to-rational extension. -/
def integralToField : PbcIntegralRing l E →+* E :=
  (algebraMap (Padic.coefficientExtensionIntegers l E) E).comp ULift.ringEquiv.toRingHom

/-- Normalized coefficient helper for completed-to-rational extension. -/
theorem coefficientAlgebraMap (a : PbcIntegralRing l E) :
    pbcRationalCoefficientEquiv l E (algebraMap _ _ a) = integralToField l E a := by
  dsimp only [pbcRationalCoefficientEquiv, RingEquiv.trans_apply]
  erw [IsLocalization.ringEquivOfRingEquiv_eq]
  exact (Padic.coefficientExtension_localization_uniformizer l E).2.choose.commutes a.down

attribute [local irreducible] pbcRationalCoefficientEquiv

private theorem completedSectionComparison (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E)))
    (U : X.ProEtᵒᵖ) (a : PbcIntegralRing l E) :
    i.hom.hom.app U (pbcCompletedSection X (pbcIntegralDatum l E) U a) =
      (integralSections l E X a).val U := by
  letI := coefficientExtensionNormedField l E
  have h := congrArg (fun f ↦ (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))) ≫ f.hom) hi
  rw [continuousCoefficientConstantComparison_unit] at h
  exact DFunLike.congr_fun (congrArg (fun f ↦ (f.app U).hom) h) a

private theorem completedScalarSquare (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    (rationalSections l E X).comp (integralToField l E) =
      (scalarLocalizationSectionsMapOfUniverses
        (i.hom ≫ integralRationalCoefficientMap l E X)).comp
          (pbcCompletedScalarSections X (pbcIntegralDatum l E)) := by
  ext a U
  change _ = (integralRationalCoefficientMap l E X).hom.app U
    (i.hom.hom.app U (pbcCompletedSection X (pbcIntegralDatum l E) U a))
  rw [completedSectionComparison l E X i hi]
  rfl

/-- Normalized coefficient helper for completed-to-rational extension. -/
theorem completedExtensionExact (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E) :
    PreservesFiniteLimits (pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)) ∧
      PreservesFiniteColimits
        (pbcExtend (i.hom ≫ integralRationalCoefficientMap l E X)) := by
  have := (extensionIsoExact i).1
  have := (extensionIsoExact i).2
  have := (integralExtensionExact l E X).1
  have := (integralExtensionExact l E X).2
  have : PreservesFiniteLimits
      (pbcExtend i.hom ⋙ pbcExtend (integralRationalCoefficientMap l E X)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (pbcExtend i.hom ⋙ pbcExtend (integralRationalCoefficientMap l E X)) :=
    comp_preservesFiniteColimits _ _
  let e := extensionComp i.hom (integralRationalCoefficientMap l E X) _ rfl
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

/-- Normalized coefficient helper for completed-to-rational extension. -/
theorem completedRestrictionLinear (X : Scheme.{u})
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    let a := i.hom ≫ integralRationalCoefficientMap l E X
    letI := scalarLocalizationCoefficientLinearOfUniverses (PbcIntegralRing l E)
      (rationalCoefficientSheaf l X E)
      ((rationalSections l E X).comp (integralToField l E))
    (pbcRestrict a).Linear (PbcIntegralRing l E) := by
  letI := scalarLocalizationCoefficientLinearOfUniverses (PbcIntegralRing l E)
    (rationalCoefficientSheaf l X E)
    ((rationalSections l E X).comp (integralToField l E))
  dsimp only
  refine { map_smul := ?_ }
  intro M N f r
  ext U x
  change (rationalSections l E X (integralToField l E r)).val U • f.val.app U x =
    ((i.hom ≫ integralRationalCoefficientMap l E X).hom.app U
    (pbcCompletedSection X (pbcIntegralDatum l E) U r)) • f.val.app U x
  exact congrArg (fun z ↦ z • f.val.app U x)
    (congrArg (fun b ↦ (b r).val U) (completedScalarSquare l E X i hi))

end
end RationalModuleLocalizationTransport
end AlgebraicGeometry.Scheme
