/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteModelProofAPI
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSerreIndConstructible
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Finiteness of direct images of constructible sheaves in degree zero -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify

attribute [local instance 20000] ProEtale.sheafBraidedCategory

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj
  Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar derivedPushHom derivedComapLowerStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

private theorem residueIdeal_maximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hg] using hm

private theorem residue_killed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : Padic.coefficientExtensionRing l E 1) ^ 1 = 0 := by
  rw [pow_one]
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change _ ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
  simpa only [pow_one, hg] using hlm

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal

private theorem finite_continuous_of_integral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (hint : ∀ M : integralConstructible ℓ E Z, ∀ q : ℤ,
      IsConstructibleModuleObject.{u + 2, u} (condensedRingObj (integralCoeff ℓ E) Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K)) := by
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E Z ⟨K, hK⟩
  have := integralScalarPushHom_isIso ℓ E p M
  let φ := coefficientMap (integralScalarMap ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K :=
    asIso ((derivedPushHom (integralScalarMap ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧)).mapIso e
  intro q
  exact constructible_derived_extend Y _ _ φ _ _ e' q (hint M q)

private theorem finite_qbar_of_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (M : PadicSubfieldConstructible Z ℓ E), ∀ q : ℤ,
      IsConstructibleModuleObject.{u + 2, u} (padicSubfieldRingObj Y ℓ E)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicAlgClRingObj Z ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj Z ℓ) K) :
    ∀ q : ℤ, IsConstructibleModuleObject.{u + 2, u} (padicAlgClRingObj Y ℓ)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K)) := by
  obtain ⟨E, M, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ ⟨K, hK⟩
  obtain ⟨N, hN⟩ := M.property.1.1
  have : M.obj.IsGE N := hN
  have := isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E p ⟨M.obj, ⟨N, hN⟩⟩
  let e₀ := (boundedConstructible (padicAlgClRingObj Z ℓ)).ι.mapIso e
  let φ := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K :=
    asIso ((derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e₀
  intro q
  exact constructible_derived_extend Y _ _ φ _ _ e' q (hfinite E M q)

private theorem finite_field_tor
    (A : Type u) [Field A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (T : Scheme.{u}) [IsNoetherian T]
    {K : DerivedCategory (FiniteDiscreteOrdinary.Internal A T)}
    (hK : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) T K) :
    _root_.DerivedCategory.finiteTorAmplitude _ K := by
  classical
  let e := (FiniteDiscreteOrdinary.encoding_exists A T).some
  have h := (FiniteDiscreteOrdinary.encoding_constructibility A T e).2 K |>.mp hK
  let B := ULift.{u + 1} A
  let J := e.fixedDerived.functor.obj K
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h.1
  obtain ⟨L, hL, ⟨i⟩⟩ := ProEtale.fixedDerivedOrigin T B J
    (fun q ↦ (FiniteDiscreteOrdinary.ordinary_constructible_iff A T _).mp (h.2 q)) a b (by
      intro q hq
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
      · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  obtain ⟨c, d, _, hv⟩ := hL.2
  have hc : L.IsGE c := (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have hd : L.IsLE d := (DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hv q (Or.inr hq)
  have hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat B) T L :=
    ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL.1 q)⟩
  obtain ⟨r, s, ht⟩ := proper_finite_field_tor B T hbc
  have ht := (_root_.DerivedCategory.torAmplitudeIn _ r s).prop_of_iso i
    ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff r s _).2 ht)
  exact ⟨min r s, s,
    ((FiniteDiscreteOrdinary.encoding_tensor_tor A T e).2.2 K _ _
      (min_le_right r s)).mpr (ht.mono (min_le_left r s) le_rfl)⟩

section Finiteness
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

private instance source_noetherian : IsNoetherian X.left :=
  isNoetherian_of_locallyOfFiniteType X.hom

private instance target_noetherian : IsNoetherian Y.left :=
  isNoetherian_of_locallyOfFiniteType Y.hom

include ℓ k

private theorem ell_unit : IsUnit (ℓ : k) :=
  isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k)
    (Fact.out : ℓ.Prime) (Fact.out : ringChar k ≠ ℓ))

set_option linter.unusedSectionVars false in
private theorem finite_etale (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : Etale.DerivedCategoryModule A X.left)
    (hK : Etale.DerivedCategory.isBoundedConstructible A X.left K) :
    Etale.DerivedCategory.isBoundedConstructible A Y.left
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K) := by
  have hA : Etale.IsSmoothBaseChangeCoefficients (ℓ ^ n) A (Spec (.of k)) := by
    refine ⟨pow_pos (Fact.out : ℓ.Prime).pos n, inferInstance, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hn
    · simpa only [map_natCast, map_pow, Nat.cast_pow] using
        ((ell_unit ℓ (k := k)).pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  exact Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    k A (ℓ ^ n) hA X.hom Y.hom f.left (Over.w f) K hK

private theorem finite_torsion (f : X ⟶ Y)
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B] (n : ℕ) (hn : (ℓ : B) ^ n = 0)
    (K : DerivedCategory (FiniteDiscreteInternalModules B X.left))
    (hK : boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj.{u} B) X.left) K) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((f.left)_*⟦Profinite.continuousMapRingObj B⟧).obj K)) := by
  classical
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  have : IsMonHom eR.hom := heR
  obtain ⟨G, hG, hforget⟩ := CategoryTheory.internalModuleAb_equivalence (ULift.{u + 1} B)
  have : G.IsEquivalence := hG
  let EX := finiteDiscreteCoefficientEquivalence B eR G hforget X.left
  let EY := finiteDiscreteCoefficientEquivalence B eR G hforget Y.left
  let A := ULift.{u + 1} B
  let νX := comparisonUpperStar (ModuleCat A) X.left
  let νY := comparisonUpperStar (ModuleCat A) Y.left
  let H := ProEtale.lowerStar (ModuleCat A) f.left
  let I := lowerStar (Profinite.continuousMapRingObj B) f.left
  let F := Etale.lowerStar (ModuleCat A) f.left
  let J := EX.inverse.mapDerivedCategory.obj K
  have hb := EX.inverse.bounded_mapDerivedCategory_obj hK.1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  have hc (q : ℤ) : ProEtale.IsConstructible A
      ((DerivedCategory.homologyFunctor _ q).obj J) := by
    have h := finiteDiscreteCoefficient_constructible B eR G hforget X.left _ (hK.2 q)
    exact ProEtale.isConstructible_of_iso
      ((EX.inverse.mapDerivedCategoryHomologyFunctorIso q).app K) h
  obtain ⟨L, hL, ⟨eL⟩⟩ := ProEtale.fixedDerivedOrigin X.left A J hc a b (by
    intro q hq
    rcases hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
    · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  let eK : K ≅ EX.functor.mapDerivedCategory.obj (νX.mapDerivedCategory.obj L) :=
    (EX.mapDerivedCategory.counitIso.app K).symm ≪≫
      EX.functor.mapDerivedCategory.mapIso eL.symm
  have hnA : (ℓ : A) ^ n = 0 := ULift.ext hn
  have hF := finite_etale ℓ f A n hnA L hL
  obtain ⟨c, d, _, hv⟩ := hL.2
  have : L.IsGE c := (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have := ProEtale.unboundedDirectImageComparison_boundedBelow A f.left L c
  let i := encodingPushforwardNatIso B eR G hforget Y.left X.left f.left
  let j : (EX.functor ⋙ I) ⋙ EY.inverse ≅ H :=
    Functor.associator _ _ _ ≪≫ Iso.inverseCompIso (G := EX.symm) i
  let k : H ⋙ EY.functor ≅ EX.functor ⋙ I :=
    (Iso.isoCompInverse (H := EY.symm) j).symm
  let d : R(H) ⋙ D(EY.functor) ≅ D(EX.functor) ⋙ R(I) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H EY.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso k ≪≫
      Functor.rightDerivedFunctorCompIso EX.functor I ≪≫
      Functor.isoWhiskerRight EX.functor.rightDerivedFunctorIsoMapDerivedCategory R(I)
  let e : EY.functor.mapDerivedCategory.obj
      (νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj L)) ≅
      I.rightDerivedFunctor.obj K :=
    EY.functor.mapDerivedCategory.mapIso
      (asIso (ProEtale.unboundedDirectImageComparisonMap A f.left
        L)) ≪≫
      d.app (νX.mapDerivedCategory.obj L) ≪≫
      I.rightDerivedFunctor.mapIso eK.symm
  intro q
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        (F.rightDerivedFunctor.obj L)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hF.1 q)
  let ec : EY.functor.obj (νY.obj ((DerivedCategory.homologyFunctor _ q).obj
      (F.rightDerivedFunctor.obj L))) ≅
      (DerivedCategory.homologyFunctor _ q).obj (I.rightDerivedFunctor.obj K) :=
    EY.functor.mapIso ((νY.mapDerivedCategoryHomologyFunctorIso q).app _) ≪≫
      (EY.functor.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e
  exact _root_.constructible_of_iso ec
    (internalComparisonConstructible B eR G hforget Y.left _)

private theorem finite_fixed (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A X.left K) :
    FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y.left
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor.obj
        K) := by
  let B := ULift.{u + 1} A
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin X.left B K
    (fun q ↦ (FiniteDiscreteOrdinary.ordinary_constructible_iff A X.left _).mp (hK.2 q)) a b (by
      intro q hq
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
      · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  have hnB : (ℓ : B) ^ n = 0 := ULift.ext hn
  have hFJ := finite_etale ℓ f B n hnB J hJ
  obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
  have : J.IsGE aJ := (DerivedCategory.isGE_iff J aJ).2 fun q hq ↦ hvJ q (Or.inl hq)
  have := ProEtale.unboundedDirectImageComparison_boundedBelow B f.left J aJ
  let νY := ProEtale.comparisonUpperStar (ModuleCat B) Y.left
  let F := Etale.lowerStar (ModuleCat B) f.left
  let G := ProEtale.lowerStar (ModuleCat B) f.left
  let e : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
      G.rightDerivedFunctor.obj K :=
    asIso (ProEtale.unboundedDirectImageComparisonMap B f.left J) ≪≫
      G.rightDerivedFunctor.mapIso eJ
  obtain ⟨c, d, _, hv⟩ := hFJ.2
  have hge : (F.rightDerivedFunctor.obj J).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have hle : (F.rightDerivedFunctor.obj J).IsLE d :=
    (DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hv q (Or.inr hq)
  have := νY.isGE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) c
  have := νY.isLE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) d
  refine ⟨⟨⟨c, DerivedCategory.TStructure.t.isGE_of_iso e c⟩,
    ⟨d, DerivedCategory.TStructure.t.isLE_of_iso e d⟩⟩, ?_⟩
  intro q
  apply (FiniteDiscreteOrdinary.ordinary_constructible_iff A Y.left _).mpr
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
  exact ProEtale.isConstructible_of_iso
    ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e)
    (ProEtale.isConstructible_comparisonUpperStar_obj _)

private theorem finite_internal (f : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (n : ℕ) (hn : (ℓ : A) ^ n = 0)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X.left))
    (hK : constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X.left K) :
    constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) Y.left
      (R((f.left)_*⟦FiniteDiscreteOrdinary.coefficient A⟧).obj K) := by
  classical
  let eX := (FiniteDiscreteOrdinary.encoding_exists A X.left).some
  let eY := (FiniteDiscreteOrdinary.encoding_exists A Y.left).some
  let e := (FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A f.left eY eX).app K
  have hsource := (FiniteDiscreteOrdinary.encoding_constructibility A X.left eX).2 K
  have himage := finite_fixed ℓ f A n hn _ (hsource.mp hK)
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y.left
      (eY.fixedDerived.functor.obj
        (R((f.left)_*⟦FiniteDiscreteOrdinary.coefficient A⟧).obj K)) := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm himage.1, ?_⟩
    intro q
    exact (FiniteDiscreteOrdinary.constructible_iso A Y.left
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)).mp (himage.2 q)
  exact (FiniteDiscreteOrdinary.encoding_constructibility A Y.left eY).2 _ |>.mpr hb

private theorem finite_integralModel
    (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (f : X ⟶ Y)
    (K : DerivedCategory (ProEtale.AdicCompletion.Modules ℓ E X.left))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) X.left K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) Y.left
      (R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  let A := Padic.coefficientExtensionRing ℓ E 1
  let : (Padic.coefficientExtensionIdeal ℓ E 1).IsMaximal := residueIdeal_maximal ℓ E
  let : Field A := Ideal.Quotient.field _
  let : Finite A := Padic.finite_coefficientExtensionRing ℓ E 1 le_rfl
  let : DiscreteTopology A := ProEtale.DerivedNakayama.quotientDiscrete ℓ E 1
  have hsource := (ProEtale.internal_integral_residue_criterion ℓ E X.left).1 K |>.mp hK
  have hkilled : (ℓ : A) ^ 1 = 0 := residue_killed ℓ E
  have hfiniteBC := finite_internal ℓ f A 1 hkilled
    ((ProEtale.AdicCompletion.derivedReduction ℓ E X.left 0).obj K) hsource.2.1
  have hfiniteTor : _root_.DerivedCategory.finiteTorAmplitude _
      (R((f.left)_*⟦ProEtale.DerivedNakayama.quotientRing ℓ E 1⟧).obj
        ((ProEtale.AdicCompletion.derivedReduction ℓ E X.left 0).obj K)) := by
    exact finite_field_tor A _ hfiniteBC
  have hlimits := ProEtale.internal_integral_direct_image_limits ℓ E f.left
  have hχ := hlimits.choose
  have hpush := hlimits.choose_spec
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (ProEtale.AdicCompletion.derivedReduction ℓ E Y.left 0).obj
      (R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj K) ≅
      R((f.left)_*⟦ProEtale.DerivedNakayama.quotientRing ℓ E 1⟧).obj
        ((ProEtale.AdicCompletion.derivedReduction ℓ E X.left 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  have hc := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing ℓ E 1) Y.left).2.1
  have ht := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing ℓ E 1) Y.left).2.2.2.1
  let := hc
  let := ht
  exact (ProEtale.internal_integral_residue_criterion ℓ E Y.left).1 _ |>.mpr
    ⟨hcomplete, (ProEtale.constantModelBoundedConstructible _ Y.left).prop_of_iso e.symm hfiniteBC,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hfiniteTor⟩

private theorem finite_integral_of_iso
    (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (ProEtale.DerivedNakayama.integerRing ℓ E))
    (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    ∀ q : ℤ, IsConstructibleModuleObject.{u + 2, u} (condensedRingObj Λ Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj (R((f.left)_*⟦Λ⟧).obj K)) := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F (X : Scheme.{u}) : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (ProEtale.DerivedNakayama.integerRing ℓ E) X) :=
    Mod.comap (coefficientMap φ X)
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  have hFK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing ℓ E) X.left ((F X.left).mapDerivedCategory.obj K) := by
    constructor
    · exact (F X.left).bounded_mapDerivedCategory_obj hK.1
    intro q
    apply (integerModel_comparison ℓ E X.left _).mp
    exact _root_.constructible_of_iso
      (((F X.left).mapDerivedCategoryHomologyFunctorIso q).app K)
      (_root_.constructible_comap (coefficientMap φ X.left) (hK.2 q))
  have hP := finite_integralModel ℓ E f _ hFK
  let hi : (F Y.left).mapDerivedCategory.obj (R((f.left)_*⟦Λ⟧).obj K) ≅
      R((f.left)_*⟦ProEtale.DerivedNakayama.integerRing ℓ E⟧).obj
        ((F X.left).mapDerivedCategory.obj K) := (derivedComapLowerStarIso φ f.left).app K
  intro q
  have hH := (integerModel_comparison ℓ E Y.left _).mpr (hP.2 q)
  have hF : IsConstructibleModuleObject
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing ℓ E) Y.left)
      ((F Y.left).obj ((DerivedCategory.homologyFunctor _ q).obj (R((f.left)_*⟦Λ⟧).obj K))) :=
    _root_.constructible_of_iso
      (((DerivedCategory.homologyFunctor _ q).mapIso hi).symm ≪≫
        ((F Y.left).mapDerivedCategoryHomologyFunctorIso q).symm.app _) hH
  let ψ := coefficientMap φ Y.left
  exact _root_.constructible_of_iso
    (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app _)
    (_root_.constructible_comap (inv ψ) hF)

end Finiteness

/-! ### The finiteness theorem, separately for each coefficient ring

`IsFinitenessCoefficient` is gone upstream: the statement is made for each coefficient ring of
Deligne's finiteness theorems, in the namespaces of upstream's per-ring operations
(`ℚ̲̄_ℓ`, `E̲`, `𝒪̲_E`) and of the finite discrete coefficient rings
(`T̲`, `O̲`). -/

section SingleConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include ℓ k

/-- The integral direct-image finiteness for the unit ball of a finite normed extension `E` of
`ℚ_ℓ`, in the form consumed by the rational and algebraic-closure cases. -/
private theorem finite_normed_integral (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (M : integralConstructible ℓ E X.left) :
    ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((f.left)_*⟦integralCoeff ℓ E⟧).obj M.obj)) := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  exact finite_integral_of_iso ℓ (ULift.{u} E) _ (integerNormedIso ℓ E)
    f M.obj M.property

/-- All higher direct images of a constructible sheaf of `ℚ̲̄_ℓ`-modules are constructible.

Source: Deligne, SGA 4½, Th. finitude 1.1; Bhatt--Scholze, Sections 6.7--6.8;
blueprint `proposition-six-operations-dctf--5`, coefficient-reduction argument.
(auxiliary; not a blueprint node)

Proof: the integral case (for the unit ball of a finite extension `E` of `ℚ_ℓ`): the sheaf is
derived complete with constructible etale reduction. Direct image preserves derived completeness
by commutation with derived inverse limits, and its reduction is the direct image of the
reduction, by the projection formula for the perfect residue-field complex. Finite-coefficient
finiteness and the reverse integral completion criterion give bounded constructible integral
direct image, hence each of its cohomology sheaves is constructible. For rational coefficients use
a bounded constructible integral model, the qcqs localization/direct-image comparison and exact
scalar extension; constructibility survives this extension. Over the algebraic closure use
finite-stage descent, direct-image comparison with scalar extension, and extension stability. No
boundedness hypothesis on the entire direct image is the conclusion of this lemma; its consumer
obtains a separate upper bound and uses truncation. -/
theorem finiteTypeDirectImage_single_constructible
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      F) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  exact finite_qbar_of_finite ℓ f.left
    (fun E M ↦ finite_continuous_of_integral ℓ E f.left (finite_normed_integral ℓ f E)
      M.obj M.property) _
    (ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
      _ 0 hF)

/-- All higher direct images of a constructible sheaf of `E̲`-modules, `E` a finite normed
extension of `ℚ_ℓ`, are constructible (the rational case of
`finiteTypeDirectImage_single_constructible`: a bounded constructible integral model, the qcqs
localization/direct-image comparison and exact scalar extension). -/
theorem ContinuousMapRingObj.finiteTypeDirectImage_single_constructible
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  exact finite_continuous_of_integral ℓ E f.left (finite_normed_integral ℓ f E) _
    (ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
      _ 0 hF)

/-- All higher direct images of a constructible sheaf of `𝒪̲_E`-modules, `E ⊆ ℚ̄_ℓ` a finite
subextension of `ℚ_ℓ`, are constructible (the integral case of
`finiteTypeDirectImage_single_constructible`, transported along the coefficient-realization
isomorphism). -/
theorem PadicIntegersRingObj.finiteTypeDirectImage_single_constructible
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  obtain ⟨e⟩ := ProEtale.integralCoefficientIso.{u} ℓ E
  exact finite_integral_of_iso ℓ (ULift.{u} E) _
    (e.symm ≪≫ integerLatticeIso ℓ (ULift.{u} E)) f _
    (ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
      _ 0 hF)

/-- All higher direct images of a constructible sheaf of `O̲`-modules, `O` the closed unit ball of
a finite normed extension `E` of `ℚ_ℓ`, are constructible (the integral case of
`finiteTypeDirectImage_single_constructible`). -/
theorem UnitBallRingObj.finiteTypeDirectImage_single_constructible
    {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((R((f.left)_*⟦Profinite.continuousMapRingObj O⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  have h : O = continuousIntegers ℓ E := by
    ext x
    rw [hO.out]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  subst O
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  exact finite_integral_of_iso ℓ (ULift.{u} E) _ (integerNormedIso ℓ E) f _
    (ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
      _ 0 hF)

/-- All higher direct images of a constructible sheaf of `T̲`-modules, `T` a finite discrete ring
in which `ℓ` is nilpotent, are constructible: identify the sheaf with its etale constructible
model; the etale/pro-etale derived comparison and Deligne's finite-coefficient theorem give
constructible cohomology of its direct image. -/
theorem FiniteDiscreteRingObj.finiteTypeDirectImage_single_constructible
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [hT : Fact (IsNilpotent (ℓ : T))]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left) F) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) Y.left)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((R((f.left)_*⟦Profinite.continuousMapRingObj T⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  obtain ⟨n, hn⟩ := hT.out
  exact finite_torsion ℓ f T n hn _
    (ProEtale.CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
      _ 0 hF)

end SingleConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
