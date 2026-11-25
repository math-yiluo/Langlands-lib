/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.ConstantToContinuousScalarFlat
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelFreeComplexReduction

/-! # Specified finite-model chart comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem double_resolution {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (S : ShortComplex C) (hS : S.ShortExact) :
    Nonempty
      (DerivedCategory.Q.obj (HomologicalComplex.double S.f
        (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)) ≅
      (DerivedCategory.singleFunctor C 0).obj S.X₃) := by
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let K : CochainComplex C ℤ := HomologicalComplex.double S.f hrel
  let e₁ : K.X (-1) ≅ S.X₁ := HomologicalComplex.doubleXIso₀ S.f hrel
  let e₀ : K.X 0 ≅ S.X₂ := HomologicalComplex.doubleXIso₁ S.f hrel (by decide)
  let L := (CochainComplex.singleFunctor C 0).obj S.X₃
  let e : L.X 0 ≅ S.X₃ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃
  let ε : K ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by decide)
    (0 : S.X₁ ⟶ L.X (-1)) (S.g ≫ e.inv)
    (by simp) (by intros; simp [L])
  have hK (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X S.f hrel i h₁ h₀
  have hd : K.d (-1) 0 = e₁.hom ≫ S.f ≫ e₀.inv :=
    HomologicalComplex.double_d S.f hrel (by decide)
  have hε : ε.f 0 = e₀.hom ≫ S.g ≫ e.inv := by
    dsimp [ε]
    simp only [HomologicalComplex.mkHomFromDouble_f₁]
    rfl
  have hqi : QuasiIso ε := by
    have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₃ i hi
    have hmono : Mono (K.d (-1) 0) := by
      have := hS.mono_f
      rw [hd]
      infer_instance
    have hepi : Epi (ε.f 0) := by
      have := hS.epi_g
      rw [hε]
      infer_instance
    have hw : K.d (-1) 0 ≫ ε.f 0 = 0 := by
      rw [hd, hε]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [S.zero_assoc]
      simp
    let S' := ShortComplex.mk (K.d (-1) 0) (ε.f 0) hw
    let φ : S ⟶ S' :=
      { τ₁ := e₁.inv
        τ₂ := e₀.inv
        τ₃ := e.inv
        comm₁₂ := by dsimp [S']; rw [hd]; simp
        comm₂₃ := by dsimp [S']; rw [hε]; simp }
    have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
    have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
    have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
    have hex : S'.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS.exact
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hK 1 (by decide) (by decide)).eq_of_tgt _ _)
        ((hL (-1) (by decide)).eq_of_src _ _)
        ((hL 1 (by decide)).eq_of_tgt _ _)).2
      exact ⟨hex, hepi⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hi' : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _
          ((hK (-2) (by decide) (by decide)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hK i hi' hi)
  exact ⟨asIso (DerivedCategory.Q.map ε) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app S.X₃).symm⟩

private theorem model_exact (T : Scheme.{u}) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    PreservesFiniteLimits (FiniteConstantModel.modelFunctor (A l E) T) ∧
      PreservesFiniteColimits (FiniteConstantModel.modelFunctor (A l E) T) ∧
      (FiniteConstantModel.modelFunctor (A l E) T).Additive := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hpid : IsPrincipalIdealRing (A l E) := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.1
  have := hpid
  apply FiniteConstantModel.modelFunctor_exact (A l E) T
  apply FiniteConstantModel.constantToContinuous_preservesFiniteLimits (A l E)
    (FiniteConstantModel.scalarToContinuous (A l E))
  intro S a
  have h := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (A l E))))
    (Profinite.continuousCoefficientRingObj (A l E))).apply_symm_apply
      (FiniteConstantModel.constantFunctions (A l E))
  exact ConcreteCategory.congr_hom (congr_app h S) a

private theorem pullback_reduction
    (V T : Scheme.{u}) (f : T ⟶ V) (M : AdicCompletion.Modules l E V) (n : ℕ) :
    Nonempty
      (((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.quotientRing l E (n + 1))
          f).obj (reduction l E V M n)) ≅
        reduction l E T ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M)
          n) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let φ := DerivedNakayama.reductionRing l E (n + 1)
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let G := CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1)) f
  have := FreeParameterEvaluation.scalarPullComparison_isIso
    (Mon.mk (DerivedNakayama.integerRing l E))
    (Mon.mk (DerivedNakayama.quotientRing l E (n + 1))) φ f K
  let c := asIso (FreeParameterEvaluation.scalarPullComparison
    (Mon.mk (DerivedNakayama.integerRing l E))
    (Mon.mk (DerivedNakayama.quotientRing l E (n + 1))) φ f K)
  exact ⟨(G.leftDerivedFunctorIsoMapDerivedCategory.app _ ) ≪≫ c.symm ≪≫
    (AdicCompletion.derivedReduction l E T n).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app M)⟩

/-- A specified scalar resolution computes the restriction of derived reduction.

Source: blueprint latest, ctf-equals-bc, Local models; Stacks Tags 093M, 06YQ,
06YY and 0G7E (blueprint: lem-sfb-finite-model-quotient-chart-comparison).

Proof: identify the coefficient pullbacks and actual quotient morphisms using
upperStarFromPointComp and cartesianCoefficients. Resolve M[0] by a flat-term
K-flat complex. Its pullback is still K-flat, and the scalar inverse-image tensor
comparison identifies restriction of reduction with reduction of the restricted
module. On T, extend the specified exact sequence along the flat map from the
constant integral ring to B_T. Constant finite free presentation extension keeps
its original differential. The resulting two-term complex is K-flat and resolves
the given model. Derived change of rings therefore computes its reduction in the
quotient coefficient category. On each basis vector its differential has entries
given by the actual quotient homomorphism. The normalized encoding identifies
this complex with ordinaryComplex, and its inverse gives the displayed isomorphism.
No constructibility or quasi-compactness is required for this chart calculation.
-/
theorem chart_comparison
    (V T : Scheme.{u}) (f : T ⟶ V) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (e : Encoding l E n T) (P : ModuleCat.{u + 1} (A l E))
    (eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj M ≅
      model l E T P)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
    (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
    (hinj : Function.Injective (integralDifferential l E a b v).hom)
    (hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
    (hsurj : Function.Surjective w.hom) :
    Nonempty
      (((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.quotientRing l E (n + 1))
          f).obj (reduction l E V M n)) ≅ internalComplex l E T n a b v e) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨hlim, hcolim, hadd⟩ := model_exact l E T
  have := hlim
  have := hcolim
  have := hadd
  let F := FiniteConstantModel.modelFunctor (A l E) T
  have hw : integralDifferential l E a b v ≫ w = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hexact ((integralDifferential l E a b v).hom x)).2 ⟨x, rfl⟩
  let S := ShortComplex.mk (integralDifferential l E a b v) w hw
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hexact
      mono_f := (ModuleCat.mono_iff_injective _).2 hinj
      epi_g := (ModuleCat.epi_iff_surjective _).2 hsurj }
  obtain ⟨eRes⟩ := double_resolution (S.map F) (hS.map_of_exact F)
  obtain ⟨eChart⟩ := pullback_reduction l E V T f M n
  obtain ⟨eFree⟩ := free_complex_reduction l E T n e a b v
  exact ⟨eChart ≪≫ (AdicCompletion.derivedReduction l E T n).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso eP ≪≫ eRes.symm) ≪≫ eFree⟩

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
