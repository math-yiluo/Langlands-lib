import Langlands.Global.RankinSelberg.FiniteWhittakerModelAssembly
import Langlands.Global.RankinSelberg.FiniteWhittakerPartialDomain
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction

/-! # Actual finite coefficient products with a joint infinite Whittaker residual -/

noncomputable section
open scoped TensorProduct Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerSemilocal

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL UnipotentClass
open FiniteWhittakerTensor FiniteWhittakerModel FiniteWhittakerPartialDomain

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance semilocalWhittakerSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance semilocalWhittakerSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance semilocalWhittakerRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance semilocalWhittakerContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance semilocalWhittakerSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance semilocalWhittakerFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance semilocalWhittakerStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance semilocalWhittakerSpaceGroup (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance semilocalWhittakerDecEq : DecidableEq (FinitePlace F) := Classical.decEq _

variable (S : Finset (FinitePlace F))

/-- The actual point with the original infinite components and all finite components one. -/
def infinitePoint (g : Points F (r + 1)) : Points F (r + 1) :=
  adelicSplit F (r + 1) S (((adelicSplit F (r + 1) S).symm g).1, (1, 1))

/-- The finite adelic element with the original S components and identity elsewhere. -/
def localFinite (g : Points F (r + 1)) : FiniteAdelicGL F (r + 1) :=
  (splitAtPlaces F (r + 1) (· ∈ S)).symm (((adelicSplit F (r + 1) S).symm g).2.1, 1)

omit [CompactSpace (AdeleQuotient F)] in
theorem infinitePoint_finite (g : Points F (r + 1)) (v : S) :
    finiteComponent F (r + 1) v (infinitePoint S g) = 1 :=
  finiteComponent_adelicSplit_of_mem F (r + 1) S _ v.property

omit [CompactSpace (AdeleQuotient F)] in
theorem localFinite_at_S (g : Points F (r + 1)) (v : S) :
    localProjection F (r + 1) v (localFinite S g) = finiteComponent F (r + 1) v g := by
  rw [localFinite, localProjection_splitAtPlaces_symm_of_pos F (r + 1) (· ∈ S) _ v.property]
  have h := finiteComponent_adelicSplit_of_mem F (r + 1) S ((adelicSplit F (r + 1) S).symm g) v.property
  simpa only [ContinuousMulEquiv.apply_symm_apply] using h.symm

omit [CompactSpace (AdeleQuotient F)] in
theorem localFinite_away (g : Points F (r + 1)) (v : FinitePlace F) (hv : v ∉ S) :
    localProjection F (r + 1) v (localFinite S g) = 1 :=
  localProjection_splitAtPlaces_symm_of_neg F (r + 1) (· ∈ S) _ hv

omit [CompactSpace (AdeleQuotient F)] in
theorem retainedPoint_eq (g : Points F (r + 1)) :
    retainedPoint S g = infinitePoint S g *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) (localFinite S g)) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, MulEquiv.apply_symm_apply]
  change GeneralLinearGroupPoints.adelicEquiv F (r + 1)
    (adelicSplit F (r + 1) S (((adelicSplit F (r + 1) S).symm g).1,
      (((adelicSplit F (r + 1) S).symm g).2.1, 1))) = _
  rw [adelicEquiv_adelicSplit]
  change _ = GeneralLinearGroupPoints.adelicEquiv F (r + 1)
    (adelicSplit F (r + 1) S (((adelicSplit F (r + 1) S).symm g).1, (1, 1))) * _
  rw [adelicEquiv_adelicSplit]
  apply AdelicGL.ext_infinite_finite F (r + 1)
  · simp [AdelicGL.infinite_pair]
  · simp [AdelicGL.finite_pair, localFinite]


/-- Invert a finite local character using its canonical field topology. -/
def inverseFinite (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :
    Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v) := by
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  exact inverseCharacter ψv

omit [CompactSpace (AdeleQuotient F)] in
/-- Inversion respects the actual canonical finite additive component. -/
theorem canonical_inverse (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hψv : ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v ψv) :
    ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent
      (inverseCharacter ψ) v (inverseFinite v ψv) := by
  let := (CompletionPadic.padicField v).canonicalTopologicalData.topology
  intro x
  change (ψv.toAddChar⁻¹) x = (ψ.toAddChar⁻¹) _
  simp only [AddChar.inv_apply']
  exact congrArg (fun z : Circle => z⁻¹) (hψv x)

variable {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
  (hPS : P.exceptional ⊆ S)

/-- Separate every retained finite component while keeping the infinite variables joint. -/
theorem coefficient_eq_product_at_retained
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (a : ∀ v : S, P.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) :
    cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) (retainedPoint S g) =
      (∏ v : S, (ℓ v).val ((P.localFactor v).representation (finiteComponent F (r + 1) v g) (a v))) *
        cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g) := by
  have h := translated_coefficient_eq_product P hP S hPS ψ hψF ψv hψv ℓ a₀ ha₀
    (infinitePoint S g) (infinitePoint_finite S g) (localFinite S g)
    (fun v hv => by rw [localFinite_away S g v hv]; exact (localIntegral F (r + 1) v).one_mem) t a
  have hlocal : (∏ v : S, (ℓ v).val ((P.localFactor v).representation
        (localProjection F (r + 1) v (localFinite S g)) (a v))) =
      ∏ v : S, (ℓ v).val ((P.localFactor v).representation (finiteComponent F (r + 1) v g) (a v)) :=
    Finset.prod_congr rfl (fun v _ => by rw [localFinite_at_S S g v])
  exact (congrArg (fun q : Points F (r + 1) => cuspWhittaker F T ψ.complex
    (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) q)
      (retainedPoint_eq S g)).trans (h.trans (congrArg (fun c : ℂ => c *
        cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g)) hlocal))


private theorem multiply_product_pairs {I : Type*} [Fintype I]
    (f f' : I → ℂ) (w w' : ℂ) :
    (∏ v, f v) * w * ((∏ v, f' v) * w') = (w * w') * ∏ v, f v * f' v := by
  rw [Finset.prod_mul_distrib]
  ring

/-- The actual opposite-character pair on the entire partial domain separates all S factors,
with exactly one as scalar, and leaves one joint infinite residual pair. -/
theorem pair_eq_product
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (a₀' : ∀ v : S, P'.localFactor v) (ha₀' : ∀ v, (ℓ' v).val (a₀' v) = 1)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
    cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g *
      cuspWhittaker F T' ψ.complex⁻¹
        (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')) g =
      (cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g) *
       cuspWhittaker F T' ψ.complex⁻¹
        (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] t')) (infinitePoint S g)) *
      ∏ v : S,
        ((ℓ v).val ((P.localFactor v).representation (finiteComponent F (r + 1) v g) (a v)) *
         (ℓ' v).val ((P'.localFactor v).representation (finiteComponent F (r + 1) v g) (a' v))) := by
  have hinvF : ∀ x : F, inverseCharacter ψ (algebraMap F (Adeles F) x) = 1 := by
    intro x
    rw [inverseCharacter_apply, hψF, inv_one]
  have hfirst := coefficient_eq_product_at_retained S P hP hPS ψ hψF ψv hψv ℓ a₀ ha₀ a t g
  have hsecond := coefficient_eq_product_at_retained S P' hP' hPS' (inverseCharacter ψ) hinvF
    (fun v => inverseFinite v.1 (ψv v)) (fun v => canonical_inverse ψ v.1 (ψv v) (hψv v))
    ℓ' a₀' ha₀' a' t' g
  simp only [complex_inverseCharacter] at hsecond
  have hpair := whittaker_pair_eq_retained P hP S hPS T' P' hP' hPS' ψ.complex
    (UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψF) a a' t t' g hg
  exact hpair.trans ((congrArg₂ (fun z w : ℂ => z * w) hfirst hsecond).trans
    (multiply_product_pairs _ _ _ _))


private theorem exists_normalization {A : Type*} [AddCommGroup A] [Module ℂ A]
    (ℓ : A →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) : ∃ a, ℓ a = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, ℓ a ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  exact ⟨(ℓ a)⁻¹ • a, by simp [ha]⟩

/-- Prescribed actual embedded coefficient functions give an exact paired finite product. -/
theorem exists_prescribed_pair
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, ComponentFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, ComponentFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (hℓ : ∀ v, (ℓ v).val ≠ 0) (hℓ' : ∀ v, (ℓ' v).val ≠ 0)
    (f : ∀ v : S, (Whittaker.coefficientModel (P.localComponent v).representation (ℓ v)).toSubmodule)
    (f' : ∀ v : S, (Whittaker.coefficientModel (P'.localComponent v).representation (ℓ' v)).toSubmodule) :
    ∃ (a a₀ : ∀ v : S, P.localFactor v) (a' a₀' : ∀ v : S, P'.localFactor v),
      (∀ v : S, (factorFunctional P v.1 (ψv v) (ℓ v)).val (a₀ v) = 1) ∧
      (∀ v : S, (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val (a₀' v) = 1) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
          (f v).val.val h) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val
          ((P'.localFactor v).representation h (a' v)) = (f' v).val.val h) ∧
      ∀ (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
        (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
        (g : Points F (r + 1)), g ∈ unipotentIntegralOutside F (r + 1) S →
      cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g *
        cuspWhittaker F T' ψ.complex⁻¹
          (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')) g =
        (cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g) *
         cuspWhittaker F T' ψ.complex⁻¹
          (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] t')) (infinitePoint S g)) *
        ∏ v : S, (f v).val.val (finiteComponent F (r + 1) v g) *
          (f' v).val.val (finiteComponent F (r + 1) v g) := by
  let a : ∀ v : S, P.localFactor v :=
    fun v => (factorVectorData P v.1 (ψv v) (ℓ v) (f v)).val
  let a' : ∀ v : S, P'.localFactor v :=
    fun v => (factorVectorData P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v) (f' v)).val
  have ha (v : S) (h : FiniteLocalGL F (r + 1) v.1) :
      (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
        (f v).val.val h := (factorVectorData P v.1 (ψv v) (ℓ v) (f v)).property h
  have ha' (v : S) (h : FiniteLocalGL F (r + 1) v.1) :
      (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val
        ((P'.localFactor v).representation h (a' v)) = (f' v).val.val h :=
    (factorVectorData P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v) (f' v)).property h
  choose a₀ ha₀ using fun v : S => exists_normalization
    (factorFunctional P v.1 (ψv v) (ℓ v)).val (factorFunctional_ne_zero P v.1 (ψv v) (ℓ v) (hℓ v))
  choose a₀' ha₀' using fun v : S => exists_normalization
    (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val
    (factorFunctional_ne_zero P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v) (hℓ' v))
  refine ⟨a, a₀, a', a₀', ha₀, ha₀', ha, ha', fun t t' g hg => ?_⟩
  have h := pair_eq_product S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv
    (fun v => factorFunctional P v.1 (ψv v) (ℓ v))
    (fun v => factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v))
    a₀ ha₀ a₀' ha₀' a a' t t' g hg
  have hlocal :
      (∏ v : S,
        ((factorFunctional P v.1 (ψv v) (ℓ v)).val
            ((P.localFactor v).representation (finiteComponent F (r + 1) v g) (a v)) *
         (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val
            ((P'.localFactor v).representation (finiteComponent F (r + 1) v g) (a' v)))) =
      ∏ v : S, (f v).val.val (finiteComponent F (r + 1) v g) *
        (f' v).val.val (finiteComponent F (r + 1) v g) :=
    Finset.prod_congr rfl (fun v _ => congrArg₂ (fun z w : ℂ => z * w) (ha v _) (ha' v _))
  exact h.trans (congrArg (fun c : ℂ =>
    (cuspWhittaker F T ψ.complex
      (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g) *
     cuspWhittaker F T' ψ.complex⁻¹
      (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] t')) (infinitePoint S g)) * c) hlocal)


/-- Exact finite coefficient products on the full partial domain, with a joint infinite residual. -/
def SemilocalProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S),
  ∀
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (_hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (_hψv : ∀ v, ClassField.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, ComponentFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, ComponentFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (_hℓ : ∀ v, (ℓ v).val ≠ 0) (_hℓ' : ∀ v, (ℓ' v).val ≠ 0)
    (f : ∀ v : S, (Whittaker.coefficientModel (P.localComponent v).representation (ℓ v)).toSubmodule)
    (f' : ∀ v : S, (Whittaker.coefficientModel (P'.localComponent v).representation (ℓ' v)).toSubmodule),
    ∃ (a a₀ : ∀ v : S, P.localFactor v) (a' a₀' : ∀ v : S, P'.localFactor v),
      (∀ v : S, (factorFunctional P v.1 (ψv v) (ℓ v)).val (a₀ v) = 1) ∧
      (∀ v : S, (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val (a₀' v) = 1) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P v.1 (ψv v) (ℓ v)).val ((P.localFactor v).representation h (a v)) =
          (f v).val.val h) ∧
      (∀ (v : S) (h : FiniteLocalGL F (r + 1) v),
        (factorFunctional P' v.1 (inverseFinite v.1 (ψv v)) (ℓ' v)).val
          ((P'.localFactor v).representation h (a' v)) = (f' v).val.val h) ∧
      ∀ (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
        (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
        (g : Points F (r + 1)), g ∈ unipotentIntegralOutside F (r + 1) S →
      cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)) g *
        cuspWhittaker F T' ψ.complex⁻¹
          (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')) g =
        (cuspWhittaker F T ψ.complex
          (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g) *
         cuspWhittaker F T' ψ.complex⁻¹
          (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a₀' ⊗ₜ[ℂ] t')) (infinitePoint S g)) *
        ∏ v : S, (f v).val.val (finiteComponent F (r + 1) v g) *
          (f' v).val.val (finiteComponent F (r + 1) v g)

/-- Assemble the prescribed local coefficient functions without an additional product hypothesis. -/
theorem finiteWhittakerSemilocalProduct : SemilocalProductStatement.{u, uQ} := by
  intro F _ _ _ r T P hP S hPS T' P' hP' hPS' ψ hψF ψv hψv ℓ ℓ' hℓ hℓ' f f'
  exact exists_prescribed_pair S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv ℓ ℓ' hℓ hℓ' f f'

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerSemilocal
