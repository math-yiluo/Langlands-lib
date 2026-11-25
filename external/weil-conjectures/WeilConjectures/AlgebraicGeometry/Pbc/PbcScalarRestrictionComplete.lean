/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarInternalHomComplete
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import all WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence

/-! # Exact coefficient restriction preserves intrinsic completeness.

## References

* Bhatt--Scholze, Lemma 6.8.2(1)
* Stacks Tag 03DA
* Stacks Tags 0999, 099B and 0A0E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (W : Scheme.{u})

/-- The completed scalar inclusion in the coefficient presentation. -/
private theorem pbcScalarModelCoefficientSquare :
    WeilConjectures.completedCoefficientMap l E F i W ≫
        (WeilConjectures.purCoefficientIso l F W).inv =
      (WeilConjectures.purCoefficientIso l E W).inv ≫ pbcScalarCoefficientMap l E F i W := by
  let eR := WeilConjectures.purCoefficientIso l E W
  let eS := WeilConjectures.purCoefficientIso l F W
  have hmap : WeilConjectures.integralCompletedScalarMap l E F i W =
      WeilConjectures.completedCoefficientMap l E F i W := by
    apply (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).unique
    · exact (WeilConjectures.integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec
    · exact (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).exists.choose_spec
  have hsq := scalarComplete_coefficientScalar_square l E F i W
  rw [hmap] at hsq
  change eR.hom ≫ _ = pbcScalarCoefficientMap l E F i W ≫ eS.hom at hsq
  apply (Iso.comp_inv_eq eS).mpr
  rw [Category.assoc]
  exact ((Iso.inv_comp_eq eR).mpr hsq.symm).symm

-- Restriction along a composite is the composite of restrictions (identity on sections).
private def scalarRestrictionCompose {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        ((f ≫ g).hom.app U).hom rfl (M.val.obj U)).symm)
      (by intro U V h; ext x; rfl)))
    (by intro M N h; ext U x; rfl)

-- Restriction along the two composites of the coefficient square agree.
private def pbcScalarModelRestrictionIso :
    pbcRestrict (pbcScalarCoefficientMap l E F i W) ⋙
        pbcRestrict (WeilConjectures.purCoefficientIso l E W).inv ≅
      pbcRestrict (WeilConjectures.purCoefficientIso l F W).inv ⋙
        pbcRestrict (WeilConjectures.completedCoefficientMap l E F i W) := by
  let FC := adicLisseForget W
  have h : FC.map (WeilConjectures.purCoefficientIso l E W).inv ≫
      FC.map (pbcScalarCoefficientMap l E F i W) =
      FC.map (WeilConjectures.completedCoefficientMap l E F i W) ≫
        FC.map (WeilConjectures.purCoefficientIso l F W).inv := by
    rw [← FC.map_comp, ← FC.map_comp, pbcScalarModelCoefficientSquare]
  exact scalarRestrictionCompose _ _ ≪≫
    eqToIso (congrArg SheafOfModules.restrictScalars.{u + 1} h) ≪≫
    (scalarRestrictionCompose _ _).symm

/-- Derived restriction in the model commutes with the scalar restriction. -/
private def pbcScalarModelDerivedRestrictionIso (K : PbcCompletedDerived W (pbcIntegralDatum l F)) :
    (pbcDerivedRestrict (WeilConjectures.purCoefficientIso l E W).inv).obj
        ((pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W)).obj K) ≅
      (pbcDerivedRestrict (WeilConjectures.completedCoefficientMap l E F i W)).obj
        ((pbcDerivedRestrict (WeilConjectures.purCoefficientIso l F W).inv).obj K) :=
  (Functor.mapDerivedCategoryCompIso (pbcRestrict (pbcScalarCoefficientMap l E F i W))
      (pbcRestrict (WeilConjectures.purCoefficientIso l E W).inv)).app K ≪≫
    (Functor.mapDerivedCategoryNatIso (pbcScalarModelRestrictionIso l E F i W)).app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (pbcRestrict (WeilConjectures.purCoefficientIso l F W).inv)
      (pbcRestrict (WeilConjectures.completedCoefficientMap l E F i W))).symm.app K


private theorem scalarPrincipalMap
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {P : CochainComplex A ℤ} (μ : End P) :
    ∃ c : (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.PrincipalCone.completion μ) ≅
          CochainComplex.PrincipalCone.completion
            (End.of ((F.mapHomologicalComplex (.up ℤ)).map μ.asHom)),
      (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.PrincipalCone.unit μ) ≫
        c.hom = CochainComplex.PrincipalCone.unit
          (End.of ((F.mapHomologicalComplex (.up ℤ)).map μ.asHom)) := by
  classical
  let G := F.mapHomologicalComplex (.up ℤ)
  let ν := End.of (G.map μ.asHom)
  let K := fun n ↦ CochainComplex.PrincipalCone.level μ n
  let L := fun n ↦ CochainComplex.PrincipalCone.level ν n
  let e := CochainComplex.principalLevelIso F μ
  let p : G.obj (∏ᶜ K) ≅ ∏ᶜ L := PreservesProduct.iso G K ≪≫ Pi.mapIso e
  have hp (n : ℕ) : p.hom ≫ Pi.π L n = G.map (Pi.π K n) ≫ (e n).hom := by
    simp [p, PreservesProduct.iso_hom, Category.assoc]
  let f := CochainComplex.PrincipalCone.step μ
  let g := CochainComplex.PrincipalCone.step ν
  have hsq : G.map (towerTransitionEndomorphism f) ≫ p.hom =
      p.hom ≫ towerTransitionEndomorphism g := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp, ← G.map_comp_assoc]
    simp only [towerTransitionEndomorphism, Preadditive.sub_comp,
      Category.id_comp, towerProductShift, Pi.lift_comp_π, G.map_sub,
      Preadditive.sub_comp, G.map_comp, Category.assoc,
      Preadditive.comp_sub, Category.comp_id, hp]
    rw [← Category.assoc p.hom, hp, Category.assoc]
    rw [← G.map_comp_assoc, Pi.lift_comp_π, G.map_comp, Category.assoc,
      CochainComplex.principalLevelIso_step F μ n]
  have hu : G.map (CochainComplex.PrincipalCone.productUnit μ) ≫ p.hom =
      CochainComplex.PrincipalCone.productUnit ν := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp, ← G.map_comp_assoc]
    change G.map ((Pi.lift _) ≫ Pi.π K n) ≫ (e n).hom = _
    rw [Pi.lift_comp_π]
    change G.map _ ≫ (e n).hom = (Pi.lift _) ≫ Pi.π L n
    rw [Pi.lift_comp_π]
    exact CochainComplex.principalLevelIso_inr F μ n
  let c := CochainComplex.coneSquareIso (G.map (towerTransitionEndomorphism f))
    (towerTransitionEndomorphism g) p p hsq
  let i := CochainComplex.mapCoconeIso F (towerTransitionEndomorphism f) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso c
  refine ⟨i, ?_⟩
  change G.map _ ≫ (CochainComplex.mapCoconeIso F _).hom ≫ _ = _
  unfold CochainComplex.PrincipalCone.unit
  rw [← Category.assoc, CochainComplex.mapCoconeIso_lift F _ _
    (CochainComplex.PrincipalCone.productUnit_comp μ)]
  have hz : G.map (CochainComplex.PrincipalCone.productUnit μ) ≫
      G.map (towerTransitionEndomorphism f) = 0 := by
    rw [← G.map_comp]
    change G.map (CochainComplex.PrincipalCone.productUnit μ ≫
      CochainComplex.PrincipalCone.oneSubShift μ) = 0
    rw [CochainComplex.PrincipalCone.productUnit_comp, G.map_zero]
  exact (completedCoconeLift_natural B _ _ p.hom p.hom hsq (𝟙 _)
    (G.map (CochainComplex.PrincipalCone.productUnit μ))
    (CochainComplex.PrincipalCone.productUnit ν) hz
    (CochainComplex.PrincipalCone.productUnit_comp ν)
    (by simpa using hu.symm)).symm.trans (Category.id_comp _)

section LocalCriterion
attribute [local instance] WeilConjectures.IntegralOnSlice.siteCategory
  WeilConjectures.IntegralOnSlice.hasDerived

/-- The scalar inclusion sends the source uniformizer to a multiple of the target one. -/
private theorem scalarUniformizer_dvd (V : W.ProEtᵒᵖ) :
    ∃ c : (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l F W).obj.obj V,
      (WeilConjectures.completedCoefficientMap l E F i W).hom.app V
          (WeilConjectures.integralCompletionScalarValue l E W V) =
        WeilConjectures.integralCompletionScalarValue l F W V * c := by
  obtain ⟨a, e, he, hπ⟩ := WeilConjectures.integral_ramification l E F i
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  refine ⟨WeilConjectures.scalarValue l F W V
    ((a : Padic.coefficientExtensionIntegers l F) *
      Padic.coefficientExtensionUniformizer l F ^ k), ?_⟩
  have h := WeilConjectures.scalarValue_map l E W F i V (Padic.coefficientExtensionUniformizer l E)
  change _ = WeilConjectures.scalarValue l F W V (Padic.coefficientExtensionUniformizer l F) * _
  erw [h, hπ, ← map_mul]
  congr 1
  ring

end LocalCriterion

/-- Restriction along the completed scalar inclusion preserves derived completeness in
the coefficient model. -/
private theorem pbcScalarModelRestrictionComplete
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l F W))
    (hM : WeilConjectures.IsSfDerivedComplete l F W M) :
    WeilConjectures.IsSfDerivedComplete l E W
      ((pbcDerivedRestrict (WeilConjectures.completedCoefficientMap l E F i W)).obj M) := by
  classical
  rw [WeilConjectures.scalarSfLocalIff] at hM ⊢
  let φ' := WeilConjectures.completedCoefficientMap l E F i W
  let G := pbcRestrict φ'
  let σE := WeilConjectures.integralCompletionScalarValue l E W
  let σ' : ∀ V : W.ProEtᵒᵖ,
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l F W).obj.obj V :=
    fun V ↦ ConcreteCategory.hom (φ'.hom.app V) (σE V)
  have hσ' : ∀ {U V : W.ProEtᵒᵖ} (g : U ⟶ V),
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l F W).obj.map g (σ' U) =
        σ' V := by
    intro U V g
    have h1 := ConcreteCategory.congr_hom (φ'.hom.naturality g) (σE U)
    have h2 := WeilConjectures.integralScalar_natural l E W g
    change _ = ConcreteCategory.hom (φ'.hom.app V) (σE V)
    exact h1.symm.trans (congrArg (ConcreteCategory.hom (φ'.hom.app V)) h2)
  have hloc : WeilConjectures.IntegralPrincipalCone.locallyComplete l F W σ' M := by
    intro U s hs
    apply hM U s
    obtain ⟨S, hS, h⟩ := hs
    refine ⟨S, hS, fun V f hf ↦ ?_⟩
    obtain ⟨c, hc⟩ := h V f hf
    obtain ⟨d, hd⟩ := scalarUniformizer_dvd l E F i W (op V)
    refine ⟨d * c, ?_⟩
    rw [hc]
    change σ' (op V) * c = _
    rw [show σ' (op V) = _ from hd, mul_assoc]
  let Q := DerivedCategory.Q.objPreimage M
  let e : DerivedCategory.Q.obj Q ≅ M := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨μ, hμ⟩ : ∃ μ : End Q, ∀ (q : ℤ) (U : W.ProEtᵒᵖ) (x : (Q.X q).val.obj U),
      (μ.asHom.f q).val.app U x = σ' U • x := by
    let μ : Q ⟶ Q :=
      { f := fun q ↦
          { val :=
              { app := fun U ↦ ModuleCat.ofHom
                  { toFun := fun x ↦ σ' U • x
                    map_add' := fun x y ↦ smul_add _ x y
                    map_smul' := fun a x ↦ by
                      let : CommRing
                          ((WeilConjectures.IntegralOnSlice.rings l F W none).obj.obj U) :=
                        inferInstanceAs
                          (CommRing ((WeilConjectures.IntegralOnSlice.ring l F W none).obj.obj U))
                      let z : (WeilConjectures.IntegralOnSlice.rings l F W none).obj.obj U := σ' U
                      change z • (a • x) = a • (z • x)
                      rw [← mul_smul, ← mul_smul, mul_comm z a] }
                naturality := by
                  intro U V g
                  ext x
                  change σ' V • (Q.X q).val.map g x = (Q.X q).val.map g (σ' U • x)
                  rw [PresheafOfModules.map_smul]
                  erw [hσ' g] } }
        comm' := by
          intro a b _hab
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro U
          ext x
          exact ((Q.d a b).val.app U).hom.map_smul (σ' U) x }
    exact ⟨End.of μ, fun q U x ↦ rfl⟩
  have hF := (WeilConjectures.IntegralPrincipalCone.localCriterion l F W σ' hσ' Q μ hμ M e).2.mp
    hloc
  have hu : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) :=
    IsIso.of_isIso_comp_left e.inv _
  have := (pbcScalarAdjunction φ').rightAdjoint_preservesLimits
  obtain ⟨c, hc⟩ := scalarPrincipalMap G μ
  let ν := End.of ((G.mapHomologicalComplex (.up ℤ)).map μ.asHom)
  have hG : IsIso (DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map (CochainComplex.PrincipalCone.unit μ))) := by
    have h := G.mapDerivedCategoryFactors.hom.naturality (CochainComplex.PrincipalCone.unit μ)
    have h' : DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map (CochainComplex.PrincipalCone.unit μ)) =
        inv (G.mapDerivedCategoryFactors.hom.app Q) ≫
          G.mapDerivedCategory.map (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ)) ≫
          G.mapDerivedCategoryFactors.hom.app _ := by
      rw [IsIso.eq_inv_comp]
      exact h.symm
    rw [h']
    infer_instance
  have hν : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit ν)) := by
    rw [← hc, Functor.map_comp]
    infer_instance
  let e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      G.mapDerivedCategory.obj M :=
    (G.mapDerivedCategoryFactors.app Q).symm ≪≫ G.mapDerivedCategory.mapIso e
  apply (WeilConjectures.IntegralPrincipalCone.localCriterion l E W σE
    (WeilConjectures.integralScalar_natural l E W) ((G.mapHomologicalComplex (.up ℤ)).obj Q) ν
    (fun q U x ↦ hμ q U x) _ e').2.mpr
  infer_instance

/-- Exact coefficient restriction preserves intrinsic completeness. -/
theorem pbcScalarRestrictionComplete (K : PbcCompletedDerived W (pbcIntegralDatum l F))
    (hK : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F) K) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W)).obj K) := by
  have hc := (WeilConjectures.purCoefficientModel_predicates l F W K).2.mp hK
  have hB := pbcScalarModelRestrictionComplete l E F i W _ hc
  apply (WeilConjectures.purCoefficientModel_predicates l E W _).2.mpr
  exact WeilConjectures.complete_of_iso l E W
    (pbcScalarModelDerivedRestrictionIso l E F i W K).symm hB

end AlgebraicGeometry.Scheme
