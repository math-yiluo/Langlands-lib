/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.RationalModuleLocalizationTransport.RationalModuleLocalizationCoefficients
import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTriangulation
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantDerivedScalarFactorization
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Transport of rational module localization

The completed presentation is compared with the continuous coefficient presentation.

## References

* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

open RationalModuleLocalizationTransport

private theorem derivedScalarCompat
    (T : Scheme.{u}) (A : Type v) (B : Type w) [CommRing A] [CommRing B]
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (b : B →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    (c : A →+* B) (hc : b.comp c = a)
    [HasDerivedCategory.{u + 2} (proEtaleRingModules T S)] :
    letI := scalarLocalizationDerivedLinearOfUniverses A S a
    letI := scalarLocalizationDerivedLinearOfUniverses B S b
    ∀ (X Y : DerivedCategory (proEtaleRingModules T S)) (f : X ⟶ Y) (r : A),
      r • f = c r • f := by
  let := scalarLocalizationCoefficientLinearOfUniverses A S a
  let := scalarLocalizationCoefficientLinearOfUniverses B S b
  let := scalarLocalizationDerivedLinearOfUniverses A S a
  let := scalarLocalizationDerivedLinearOfUniverses B S b
  intro X Y f r
  let D := DerivedCategory (proEtaleRingModules T S)
  have h : (Linear.toCatCenter A D r).asHom = (Linear.toCatCenter B D (c r)).asHom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    intro K
    have hK : (r • 𝟙 K : K ⟶ K) = c r • 𝟙 K := by
      ext n U z
      change (a r).val U • z = (b (c r)).val U • z
      rw [← RingHom.comp_apply, hc]
    change r • 𝟙 (DerivedCategory.Q.obj K) = c r • 𝟙 (DerivedCategory.Q.obj K)
    have hq := congrArg (fun g : K ⟶ K ↦ DerivedCategory.Q.map g) hK
    simp only [Functor.map_smul] at hq
    erw [CategoryTheory.Functor.map_id] at hq
    exact hq
  have hX := congrArg (fun z ↦ z.app X) h
  change r • 𝟙 X = c r • 𝟙 X at hX
  calc
    r • f = (r • 𝟙 X) ≫ f := by simp
    _ = (c r • 𝟙 X) ≫ f := congrArg (fun g ↦ g ≫ f) hX
    _ = c r • f := by simp

section Fractions
open scoped TensorProduct
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
  {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
  [Linear A D] [Linear B D'] (t : A) (φ : Localization.Away t →+* B)
  (F : D ⥤ D') [F.Additive]
  (hF : ∀ (X Y : D) (r : A) (f : X ⟶ Y),
    F.map (r • f) = φ (algebraMap A (Localization.Away t) r) • F.map f)

private def transportFractionHom (X Y : D) :
    (Localization.Away t ⊗[A] (X ⟶ Y)) →+ (F.obj X ⟶ F.obj Y) := by
  let β : Localization.Away t →+ (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
    { toFun := fun b ↦
        { toFun := fun f ↦ φ b • F.map f
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      map_zero' := by ext f; simp
      map_add' := by intros; ext f; simp [add_smul] }
  apply TensorProduct.liftAddHom β
  intro r b f
  dsimp [β]
  rw [Algebra.smul_def, map_mul, hF, smul_smul, mul_comm]

private theorem transportFractionHom_tmul (X Y : D)
    (b : Localization.Away t) (f : X ⟶ Y) :
    transportFractionHom t φ F hF X Y (b ⊗ₜ[A] f) = φ b • F.map f := by
  rfl

private def transportFractionFunctor : ScalarLocalization A D t ⥤ D' where
  obj X := F.obj X.obj
  map {X Y} f := transportFractionHom t φ F hF X.obj Y.obj f
  map_id X := by
    change transportFractionHom t φ F hF _ _ (1 ⊗ₜ[A] 𝟙 X.obj) = _
    rw [transportFractionHom_tmul, map_one, one_smul, F.map_id]
  map_comp {X Y Z} f g := by
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        change transportFractionHom t φ F hF _ _
          (ScalarLocalization.composition A D t _ _ _ (b ⊗ₜ[A] g) (a ⊗ₜ[A] f)) = _
        simp only [ScalarLocalization.composition_tmul, transportFractionHom_tmul,
          F.map_comp, map_mul, Linear.smul_comp, Linear.comp_smul, smul_smul]
      | add f f' hf hf' =>
        rw [Preadditive.add_comp X Y Z f f' (b ⊗ₜ[A] g)]
        simp only [map_add, hf, hf', Preadditive.add_comp]
    | add g g' hg hg' =>
      rw [Preadditive.comp_add X Y Z f g g']
      simp only [map_add, hg, hg', Preadditive.comp_add]

private theorem transportFractionFunctor_additive :
    (transportFractionFunctor t φ F hF).Additive where
  map_add := (transportFractionHom t φ F hF _ _).map_add _ _

private theorem transportFractionFunctor_smul
    (X Y : ScalarLocalization A D t) (r : Localization.Away t) (f : X ⟶ Y) :
    (transportFractionFunctor t φ F hF).map (r • f) =
      φ r • (transportFractionFunctor t φ F hF).map f := by
  change transportFractionHom t φ F hF X.obj Y.obj (r • f) =
    φ r • transportFractionHom t φ F hF X.obj Y.obj f
  induction f using TensorProduct.inductionOn with
  | tmul b f =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [transportFractionHom_tmul, map_mul, mul_smul]
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]

private theorem transportFractionFunctor_integral (X Y : D) (f : X ⟶ Y) :
    (transportFractionFunctor t φ F hF).map ((ScalarLocalization.localization A D t).map f) =
      F.map f := by
  change transportFractionHom t φ F hF X Y (1 ⊗ₜ[A] f) = F.map f
  rw [transportFractionHom_tmul, map_one, one_smul]

private theorem transportFractionFunctor_obj (X : ScalarLocalization A D t) :
    (transportFractionFunctor t φ F hF).obj X = F.obj X.obj := rfl

private def transportFractionFactors :
    ScalarLocalization.localization A D t ⋙ transportFractionFunctor t φ F hF ≅ F :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (by
    intro X Y f
    change transportFractionHom t φ F hF X Y (1 ⊗ₜ[A] f) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp only [transportFractionHom_tmul, map_one, one_smul, Category.comp_id,
      Category.id_comp])

end Fractions

attribute [local irreducible] reductionDerivedChange reductionChange transportFractionHom
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

private theorem descendTriangulated
    {C L D : Type*} [Category C] [Category L] [Category D]
    [Preadditive C] [Preadditive L] [Preadditive D]
    [HasZeroObject C] [HasZeroObject L] [HasZeroObject D]
    [HasShift C ℤ] [HasShift L ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor L n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated L] [Pretriangulated D]
    (Q : C ⥤ L) (W : MorphismProperty C) [Q.IsLocalization W] [Q.CommShift ℤ]
    (H : C ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (J : L ⥤ D) (fac : Q ⋙ J ≅ H)
    (hdist : ∀ Δ : Triangle L, Δ ∈ distTriang L →
      ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧ Nonempty (Δ ≅ Q.mapTriangle.obj Δ₀)) :
    ∃ s : J.CommShift ℤ, letI := s; J.IsTriangulated := by
  letI : Localization.Lifting Q W H J := ⟨fac⟩
  let s : J.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ H J
  letI := s
  have : NatTrans.CommShift fac.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q W ℤ H J
  refine ⟨s, ⟨?_⟩⟩
  intro Δ hΔ
  obtain ⟨Δ₀, hΔ₀, ⟨j⟩⟩ := hdist Δ hΔ
  have : (Q ⋙ J).IsTriangulated :=
    (Functor.isTriangulated_iff_of_iso fac).2 inferInstance
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    ((Q ⋙ J).map_distinguished Δ₀ hΔ₀) _
    (J.mapTriangle.mapIso j ≪≫ (Functor.mapTriangleCompIso Q J).symm.app Δ₀)

private theorem completedFractionDescent (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (_hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    letI := rationalLinear l E X
    let α := i.hom ≫ integralRationalCoefficientMap l E X
    ∀ [_hs : (pbcDerivedExtend α).CommShift ℤ] [_ht : (pbcDerivedExtend α).IsTriangulated],
    ∃ J : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
        DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      ∃ (_ha : J.Additive) (_hl : J.Linear E) (hs : J.CommShift ℤ),
        letI := hs
        J.IsTriangulated ∧
        ∃ hobj : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
            J.obj ((pbcRationalization X (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj K) = (pbcDerivedExtend.{u} α).obj K.obj,
          ∀ (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
            (f : K ⟶ L) (n : ℕ),
            J.map (((pbcRationalCoefficientEquiv l E).symm
              (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
                (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
              eqToHom (hobj K) ≫
                (((pbcUniformizer l E).down.val ^ n)⁻¹ •
                  (pbcDerivedExtend.{u} α).map f.hom) ≫ eqToHom (hobj L).symm := by
  classical
  letI := rationalLinear l E X
  let α := i.hom ≫ integralRationalCoefficientMap l E X
  dsimp only
  intro hs ht
  let A := PbcIntegralRing l E
  let t := pbcUniformizer l E
  let : Module A (Localization.Away t) := OreLocalization.instModuleOfIsScalarTower
  let S := rationalCoefficientSheaf l X E
  let b := rationalSections l E X
  let c := integralToField l E
  let a := b.comp c
  letI := scalarLocalizationCoefficientLinearOfUniverses A S a
  have : (pbcRestrict α).Linear A := completedRestrictionLinear l E X i _hi
  have : (pbcDerivedRestrict α).Linear A :=
    inferInstanceAs ((pbcRestrict α).mapDerivedCategory.Linear A)
  have : (pbcDerivedExtend α).Linear A :=
    (pbcDerivedScalarAdjunction α).left_adjoint_linear
  let D := PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)
  let P : ObjectProperty (PbcCompletedDerived X (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
  have : (pbcDerivedRestrict α).Additive :=
    inferInstanceAs ((pbcRestrict α).mapDerivedCategory.Additive)
  have : (pbcDerivedExtend α).Additive :=
    (pbcDerivedScalarAdjunction α).left_adjoint_additive
  have : P.IsTriangulated := pbcIntegralTriangulated l E X Fact.out Fact.out
  have : P.ι.IsTriangulated := by
    constructor
    intro Δ hΔ
    exact hΔ
  let H := P.ι ⋙ pbcDerivedExtend α
  have hHtri : H.IsTriangulated := by
    constructor
    intro Δ hΔ
    exact isomorphic_distinguished _
      (ht.map_distinguished (P.ι.mapTriangle.obj Δ) hΔ) _
      ((Functor.mapTriangleCompIso P.ι (pbcDerivedExtend α)).app Δ)
  have : H.Additive := inferInstanceAs (P.ι ⋙ pbcDerivedExtend α).Additive
  have hH : ∀ (K L : D) (r : A) (f : K ⟶ L),
      H.map (r • f) =
        (pbcRationalCoefficientEquiv l E) (algebraMap A (Localization.Away t) r) •
          H.map f := by
    intro K L r f
    change (pbcDerivedExtend α).map (r • f.hom) = _
    rw [(pbcDerivedExtend α).map_smul]
    exact (derivedScalarCompat X A E S a b c rfl _ _ _ r).trans
      (congrArg (fun z : E ↦ z • (pbcDerivedExtend α).map f.hom)
        (coefficientAlgebraMap l E r).symm)
  let J := transportFractionFunctor t (pbcRationalCoefficientEquiv l E).toRingHom H hH
  have hJadd : J.Additive := transportFractionFunctor_additive _ _ _ _
  have hJlin : J.Linear E := by
    constructor
    intro K L f z
    change J.map ((pbcRationalCoefficientEquiv l E).symm z • f) = z • J.map f
    exact (transportFractionFunctor_smul t (pbcRationalCoefficientEquiv l E).toRingHom
      H hH K L ((pbcRationalCoefficientEquiv l E).symm z) f).trans
        (congrArg (fun a : E ↦ a • J.map f)
          ((pbcRationalCoefficientEquiv l E).apply_symm_apply z))
  let Q := pbcRationalization X (pbcIntegralDatum l E) t
  let W := Rationalization.W (Submonoid.powers t) D
  have : Q.IsLocalization W :=
    ScalarLocalization.pbcScalarLocalization_isLocalization A D t
  let fac : Q ⋙ J ≅ H := transportFractionFactors t
    (pbcRationalCoefficientEquiv l E).toRingHom H hH
  have hdist := ((pbcRationalTriangulationData l E X Fact.out Fact.out).choose_spec.choose_spec.2
    ).choose_spec.choose_spec.2.choose_spec.2.2
  letI := hHtri
  obtain ⟨sJ, hJtri⟩ := descendTriangulated Q W H J fac (fun Δ ↦ (hdist Δ).1)
  letI := sJ
  refine ⟨J, hJadd, hJlin, sJ, hJtri,
    (fun K ↦ transportFractionFunctor_obj t
      (pbcRationalCoefficientEquiv l E).toRingHom H hH ⟨K⟩), ?_⟩
  intro K L f n
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  let x := ((pbcUniformizer l E).down.val ^ n)⁻¹
  exact (transportFractionFunctor_smul t (pbcRationalCoefficientEquiv l E).toRingHom
    H hH ⟨K⟩ ⟨L⟩ ((pbcRationalCoefficientEquiv l E).symm x) (Q.map f)).trans
      ((congrArg (fun a : E ↦ a • J.map (Q.map f))
        ((pbcRationalCoefficientEquiv l E).apply_symm_apply x)).trans
          (congrArg (fun g ↦ x • g)
            (transportFractionFunctor_integral t
              (pbcRationalCoefficientEquiv l E).toRingHom H hH K L f)))

/-- Exact derived localization and fraction descent in the completed presentation. -/
theorem rationalModuleLocalizationTransport (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (i : pbcAdicCompletion X (pbcIntegralDatum l E) ≅ integralCoefficientSheaf l X E)
    (_hi : pbcCompletedScalar X (pbcIntegralDatum l E) ≫ i.hom =
      (letI := coefficientExtensionNormedField l E
       continuousCoefficientConstantComparison X (PbcIntegralRing l E))) :
    ∃ κ : Linear E (pbcModules X (rationalCoefficientSheaf l X E)),
    letI := κ
    letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
      inferInstance
    let α : pbcAdicCompletion X (pbcIntegralDatum l E) ⟶
        rationalCoefficientSheaf l X E := i.hom ≫ integralRationalCoefficientMap l E X
    (∀ (M N : pbcModules X (rationalCoefficientSheaf l X E))
      (f : M ⟶ N) (a : E) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (a • f).val.app U x =
        (letI := coefficientExtensionNormedField l E
         (show (rationalCoefficientSheaf l X E).obj.obj U from
           ContinuousMap.const _ (ULift.up.{u + 1, u} a))) • f.val.app U x) ∧
    (PreservesFiniteLimits (pbcExtend.{u} α) ∧ PreservesFiniteColimits (pbcExtend.{u} α)) ∧
    (∃ (_ : (pbcDerivedExtend.{u} α).CommShift ℤ), (pbcDerivedExtend.{u} α).IsTriangulated) ∧
    (∀ r : ℤ, Nonempty (pbcDerivedExtend.{u} α ⋙
      DerivedCategory.homologyFunctor (pbcModules X (rationalCoefficientSheaf l X E)) r ≅
      DerivedCategory.homologyFunctor
        (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) r ⋙ pbcExtend.{u} α)) ∧
    ∃ J : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
        DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)),
      ∃ (_ha : J.Additive) (_hl : J.Linear E) (hs : J.CommShift ℤ),
        letI := hs
        J.IsTriangulated ∧
        ∃ hobj : ∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
            J.obj ((pbcRationalization X (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj K) = (pbcDerivedExtend.{u} α).obj K.obj,
          ∀ (K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
            (f : K ⟶ L) (n : ℕ),
            J.map (((pbcRationalCoefficientEquiv l E).symm
              (((pbcUniformizer l E).down.val ^ n)⁻¹)) •
                (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
              eqToHom (hobj K) ≫
                (((pbcUniformizer l E).down.val ^ n)⁻¹ •
                  (pbcDerivedExtend.{u} α).map f.hom) ≫ eqToHom (hobj L).symm := by
  classical
  let κ := rationalLinear l E X
  refine ⟨κ, ?_⟩
  letI := κ
  dsimp only
  let α := i.hom ≫ integralRationalCoefficientMap l E X
  have hα := completedExtensionExact l E X i
  letI := hα.1
  letI := hα.2
  let e := exactExtensionDerived α
  let sF : (pbcDerivedExtend α).CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  letI := sF
  have : NatTrans.CommShift e.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility e.symm ℤ
  have hFtri : (pbcDerivedExtend α).IsTriangulated :=
    Functor.isTriangulated_of_iso e.symm
  refine ⟨(fun _ _ _ _ _ _ ↦ rfl), hα, ⟨sF, hFtri⟩, ?_, ?_⟩
  · intro r
    exact ⟨Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ r) ≪≫
      ((pbcExtend α).mapDerivedCategoryHomologyFunctorIso r).symm⟩
  · exact completedFractionDescent l E X i _hi

end
end AlgebraicGeometry.Scheme
