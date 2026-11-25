import Langlands.Global.RankinSelberg.FiniteWhittakerSemilocalProduct
import Langlands.Global.RankinSelberg.ContragredientDualSplit

/-! # Ordinary and dual finite Whittaker products with the same normalization -/

noncomputable section
open scoped TensorProduct Classical CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.FiniteWhittakerDual

open Langlands.Automorphic Langlands.Global.FiniteAdelicGL UnipotentClass
open FiniteWhittakerTensor FiniteWhittakerModel FiniteWhittakerPartialDomain FiniteWhittakerSemilocal

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance finiteDualWhittakerSchemeAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance finiteDualWhittakerSchemeSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance finiteDualWhittakerRationalGroup : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerContinuousGroup : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerFormsGroup : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerStableGroup : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerSpaceGroup (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance finiteDualWhittakerDecEq : DecidableEq (FinitePlace F) := Classical.decEq _


omit [CompactSpace (AdeleQuotient F)] in
/-- The Weyl/inverse-transpose argument commutes with the actual finite component. -/
theorem finiteComponent_dualPoint (n : ℕ) (v : FinitePlace F) (g : Points F n) :
    finiteComponent F n v (Unfolding.dualPoint F n g) =
      GeneralLinear.weylLong n (FiniteCompletion F v) *
        GeneralLinear.inverseTranspose n (FiniteCompletion F v) (finiteComponent F n v g) := by
  have h : finiteComponent F n v (Unfolding.dualPoint F n g) =
      finiteComponent F n v ((GeneralLinearGroupPoints.adelicEquiv F n).symm
        (GeneralLinear.weylLong n (Adeles F))) *
        GeneralLinear.inverseTranspose n _ (finiteComponent F n v g) := by
    simp only [finiteComponent, Unfolding.dualPoint, MulEquiv.apply_symm_apply, map_mul,
      ContragredientDual.finite_inverseTranspose, ContragredientDual.localProjection_inverseTranspose]
  exact h.trans (congrArg (fun z => z *
    GeneralLinear.inverseTranspose n (FiniteCompletion F v) (finiteComponent F n v g))
      (ContragredientDualSplit.finiteComponent_weylLong F n v))

omit [CompactSpace (AdeleQuotient F)] in
/-- The long Weyl permutation is integral at every finite place. -/
theorem weylLong_mem_localIntegral (n : ℕ) (v : FinitePlace F) :
    GeneralLinear.weylLong n (FiniteCompletion F v) ∈ localIntegral F n v := by
  rw [mem_localIntegral]
  constructor <;> intro i j <;>
    simp only [GeneralLinear.weylLong_inv, GeneralLinear.weylLong_entry] <;>
    split_ifs <;> simp

omit [CompactSpace (AdeleQuotient F)] in
/-- The local partial-domain condition is preserved by the dual argument. -/
theorem isUnipotentIntegral_dual (n : ℕ) (v : FinitePlace F) (g : FiniteLocalGL F n v)
    (hg : IsUnipotentIntegral F n v g) :
    IsUnipotentIntegral F n v (GeneralLinear.weylLong n (FiniteCompletion F v) *
      GeneralLinear.inverseTranspose n (FiniteCompletion F v) g) := by
  obtain ⟨k, hk, hd, ht⟩ := hg
  have hu : g * k ∈ GeneralLinear.upperUnipotent n (FiniteCompletion F v) := ⟨ht, hd⟩
  have hui := (GeneralLinear.upperUnipotent n (FiniteCompletion F v)).inv_mem hu
  have htri := Unfolding.isUnitriangular_dualConjGL n (FiniteCompletion F v) (g * k) ⟨hui.1, hui.2⟩
  have heq : (GeneralLinear.weylLong n (FiniteCompletion F v) *
        GeneralLinear.inverseTranspose n (FiniteCompletion F v) g) *
      (GeneralLinear.inverseTranspose n (FiniteCompletion F v) k *
        GeneralLinear.weylLong n (FiniteCompletion F v)) =
      Unfolding.dualConjGL n (FiniteCompletion F v) (g * k) := by
    rw [Unfolding.dualConjGL_apply, map_mul]
    simp only [mul_assoc]
  refine ⟨_, (localIntegral F n v).mul_mem
    (ContragredientDual.inverseTranspose_mem_localIntegral F n v hk)
    (weylLong_mem_localIntegral n v), ?_, ?_⟩
  · intro i
    change ((GeneralLinear.weylLong n (FiniteCompletion F v) *
      GeneralLinear.inverseTranspose n (FiniteCompletion F v) g) *
        (GeneralLinear.inverseTranspose n (FiniteCompletion F v) k *
          GeneralLinear.weylLong n (FiniteCompletion F v))) i i = 1
    rw [heq]
    exact htri.2 i
  · intro i j hij
    change ((GeneralLinear.weylLong n (FiniteCompletion F v) *
      GeneralLinear.inverseTranspose n (FiniteCompletion F v) g) *
        (GeneralLinear.inverseTranspose n (FiniteCompletion F v) k *
          GeneralLinear.weylLong n (FiniteCompletion F v))) i j = 0
    rw [heq]
    exact htri.1 hij

omit [CompactSpace (AdeleQuotient F)] in
/-- The entire partial adelic domain is stable under the dual argument. -/
theorem dualPoint_mem_partial (n : ℕ) (S : Finset (FinitePlace F)) (g : Points F n)
    (hg : g ∈ unipotentIntegralOutside F n S) :
    Unfolding.dualPoint F n g ∈ unipotentIntegralOutside F n S := by
  intro v hv
  rw [finiteComponent_dualPoint]
  exact isUnipotentIntegral_dual n v _ (hg v hv)


variable (S : Finset (FinitePlace F)) {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible)
  (hPS : P.exceptional ⊆ S)

/-- The actual normalized global coefficient with every finite argument set to one. -/
def infiniteResidual (ψ : AddChar (Adeles F) ℂ) (a₀ : ∀ v : S, P.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) : Points F (r + 1) → ℂ :=
  fun g => cuspWhittaker F T ψ
    (P.allPlaceTensorEquiv hP (P.finitePure S hPS a₀ ⊗ₜ[ℂ] t)) (infinitePoint S g)

/-- The same normalized finite vectors separate the dual paired product. -/
theorem pair_dual_eq_product
    (T' : CuspidalOperatorRealization F r)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hP' : ∀ v, (P'.localComponent v).IsIrreducible ∧ (P'.localComponent v).IsAdmissible)
    (hPS' : P'.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v.1))
    (hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (a₀' : ∀ v : S, P'.localFactor v) (ha₀' : ∀ v, (ℓ' v).val (a₀' v) = 1)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
    (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
    dualFunction F (r + 1) (cuspWhittaker F T ψ.complex
        (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t))) g *
      dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹
        (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t'))) g =
      (dualFunction F (r + 1) (infiniteResidual S P hP hPS ψ.complex a₀ t) g *
       dualFunction F (r + 1) (infiniteResidual S P' hP' hPS' ψ.complex⁻¹ a₀' t') g) *
      ∏ v : S,
        (ArchimedeanLocal.dualFunction (r + 1)
          (fun h => (ℓ v).val ((P.localFactor v).representation h (a v))) (finiteComponent F (r + 1) v g) *
         ArchimedeanLocal.dualFunction (r + 1)
          (fun h => (ℓ' v).val ((P'.localFactor v).representation h (a' v))) (finiteComponent F (r + 1) v g)) := by
  have h := pair_eq_product S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv
    ℓ ℓ' a₀ ha₀ a₀' ha₀' a a' t t' (Unfolding.dualPoint F (r + 1) g)
    (dualPoint_mem_partial (r + 1) S g hg)
  have hlocal :
      (∏ v : S,
        ((ℓ v).val ((P.localFactor v).representation
            (finiteComponent F (r + 1) v (Unfolding.dualPoint F (r + 1) g)) (a v)) *
         (ℓ' v).val ((P'.localFactor v).representation
            (finiteComponent F (r + 1) v (Unfolding.dualPoint F (r + 1) g)) (a' v)))) =
      ∏ v : S,
        (ArchimedeanLocal.dualFunction (r + 1)
          (fun h => (ℓ v).val ((P.localFactor v).representation h (a v))) (finiteComponent F (r + 1) v g) *
         ArchimedeanLocal.dualFunction (r + 1)
          (fun h => (ℓ' v).val ((P'.localFactor v).representation h (a' v))) (finiteComponent F (r + 1) v g)) :=
    Finset.prod_congr rfl (fun v _ => by rw [finiteComponent_dualPoint]; rfl)
  exact h.trans (congrArg (fun c : ℂ =>
    (dualFunction F (r + 1) (infiniteResidual S P hP hPS ψ.complex a₀ t) g *
     dualFunction F (r + 1) (infiniteResidual S P' hP' hPS' ψ.complex⁻¹ a₀' t') g) * c) hlocal)


/-- Ordinary and dual paired products with the same two residual functions. -/
def PairedProducts (W W' R R' : Points F (r + 1) → ℂ)
    (f f' : ∀ v : S, FiniteLocalGL F (r + 1) v → ℂ) : Prop :=
  ∀ g : Points F (r + 1), g ∈ unipotentIntegralOutside F (r + 1) S →
    (W g * W' g = (R g * R' g) * ∏ v : S, f v (finiteComponent F (r + 1) v g) *
      f' v (finiteComponent F (r + 1) v g)) ∧
    (dualFunction F (r + 1) W g * dualFunction F (r + 1) W' g =
      (dualFunction F (r + 1) R g * dualFunction F (r + 1) R' g) *
        ∏ v : S, ArchimedeanLocal.dualFunction (r + 1) (f v) (finiteComponent F (r + 1) v g) *
          ArchimedeanLocal.dualFunction (r + 1) (f' v) (finiteComponent F (r + 1) v g))

/-- Joint ordinary/dual finite factorization for actual tensor vectors with normalized references. -/
def OrdinaryDualFiniteProductStatement : Prop :=
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
    (_hψv : ∀ v, ClassFieldTheory.Global.RelativeWeilGroup.IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (_ha₀ : ∀ v, (ℓ v).val (a₀ v) = 1)
    (a₀' : ∀ v : S, P'.localFactor v) (_ha₀' : ∀ v, (ℓ' v).val (a₀' v) = 1)
    (a : ∀ v : S, P.localFactor v) (a' : ∀ v : S, P'.localFactor v)
    (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u)),
    PairedProducts S
      (cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hP (P.finitePure S hPS a ⊗ₜ[ℂ] t)))
      (cuspWhittaker F T' ψ.complex⁻¹ (P'.allPlaceTensorEquiv hP' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')))
      (infiniteResidual S P hP hPS ψ.complex a₀ t)
      (infiniteResidual S P' hP' hPS' ψ.complex⁻¹ a₀' t')
      (fun v h => (ℓ v).val ((P.localFactor v).representation h (a v)))
      (fun v h => (ℓ' v).val ((P'.localFactor v).representation h (a' v)))

/-- The finite normalization is identical for the ordinary and dual products. -/
theorem ordinaryDualFiniteProduct : OrdinaryDualFiniteProductStatement.{u, uQ} := by
  intro F _ _ _ r T P hP S hPS T' P' hP' hPS' ψ hψF ψv hψv ℓ ℓ' a₀ ha₀ a₀' ha₀' a a' t t' g hg
  exact ⟨pair_eq_product S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv
    ℓ ℓ' a₀ ha₀ a₀' ha₀' a a' t t' g hg,
    pair_dual_eq_product S P hP hPS T' P' hP' hPS' ψ hψF ψv hψv
      ℓ ℓ' a₀ ha₀ a₀' ha₀' a a' t t' g hg⟩

end Langlands.Global.RankinSelbergGlobal.FiniteWhittakerDual
