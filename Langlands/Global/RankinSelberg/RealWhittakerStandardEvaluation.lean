import Langlands.Global.RankinSelberg.RealPrincipalSeriesFunctionalBound
import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Global.RankinSelberg.RealWhittakerBanachModel
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-! # Bounded standard-module evaluation of a uniform Whittaker map -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff ZeroAtInfty NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)
local notation "I" => matrixModel ℝ (r + 1)
local notation "S" ds => realStandardModule (r + 1) ds
local notation "V" ds => Automorphic.realStandardKFinite (r + 1) ds
local notation "R" ds => RealStandardCompactBanach.representation (n := r + 1) ds
local notation "D" ds => DerivativeSmoothVectors I (R ds)
local notation "P" ds => principalSeries ℝ (r + 1) (realPositionCharacter (RealPrincipalSeries.expand ds))

/-- If smooth Casselman–Wallach extension holds, uniform Whittaker coefficients
of an irreducible standard module are evaluations of its genuine smooth action. -/
theorem exists_continuous_standardEvaluation
    (hCW : RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0})
    (ds : List RealBlock) (a : ℝˣ) (B : (V ds) →ₗ[ℂ] (G → ℂ))
    (hIrr : IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds))
    (hB : IsRealUniformWhittakerIntertwiner r ds a B) :
    ∃ L : (D ds) →L[ℂ] ℂ, ∀ (f : V ds) (g : G),
      L (DerivativeSmoothVectors.representation I (R ds) g (compactFiniteEquiv ds f).val) = B f g := by
  obtain ⟨d, J, hJ, hEval⟩ := RealWhittakerBanachModel.realWhittakerBanachModel r ds a B hB
  let R₀ := HeightWeightedRightTranslation.representation (A := M) d
  obtain ⟨T, hT, hAgree⟩ := hCW r (V ds) (realStandardRep (r + 1) ds)
    (realStandardLie (r + 1) ds) (Carrier (r + 1) ds) (R ds)
    (G →C₀ ℂ) R₀ (compactFiniteEquiv ds) J hIrr (realStandardAdmissible (r + 1) ds)
    (isContinuousRepresentation ds)
    (HeightWeightedRightTranslation.heightWeightedRightTranslation M d)
    (isSmoothGKIntertwiner_compactFiniteEquiv ds) hJ
  refine ⟨(RealWhittakerBanachModel.evaluation d).comp T, fun f g => ?_⟩
  rw [ContinuousLinearMap.comp_apply, hT, hAgree]
  exact hEval f g

/-- Evaluation of a word of compact-model derivatives is the iterated right derivative. -/
theorem derivativeCLM_compactEval (ds : List RealBlock) (Xs : List M) (f : S ds)
    (k : U) :
    (derivativeCLM I (R ds) Xs (derivativeEquiv ds f)).val k =
      RealLocalWhittaker.iteratedRightDerivative r Xs f.val (Unitary.toUnits k) := by
  let F (ys : List M) (h : S ds) := ys.foldr (differentiate ds) h
  have hF (ys : List M) :
      iteratedLieDerivative I (R ds) ys (embed ds f) = embed ds (F ys f) := by
    induction ys with
    | nil => rfl
    | cons X ys ih => rw [iteratedLieDerivative_cons, ih, lieDerivative_embed]; rfl
  have hVal (ys : List M) :
      (F ys f).val = RealLocalWhittaker.iteratedRightDerivative r ys f.val := by
    induction ys with
    | nil => rfl
    | cons X ys ih =>
      change rightDerivative I X (F ys f).val =
        rightDerivative I X (RealLocalWhittaker.iteratedRightDerivative r ys f.val)
      rw [ih]
  rw [derivativeCLM_apply, toSmooth_derivativeEquiv, hF, embed_val, compactRestriction_apply, hVal]

/-- A continuous functional of genuine smooth vectors is bounded on the original
standard module by finitely many compact right-derivative suprema. -/
theorem has_compact_bound_of_continuous (ds : List RealBlock) (L : (D ds) →L[ℂ] ℂ) :
    ∃ (m : ℕ) (Xs : Fin m → List M) (A : ℝ), 0 ≤ A ∧
      ∀ (f : S ds) (c : Fin m → ℝ),
        (∀ i, ∀ k ∈ K, ‖RealLocalWhittaker.iteratedRightDerivative r (Xs i) f.val k‖ ≤ c i) →
        ‖L (derivativeEquiv ds f)‖ ≤ A * ∑ i, c i := by
  classical
  let e := toSmooth I (R ds)
  let L₀ := L.toLinearMap.comp e.symm.toLinearMap
  have hL₀ : Continuous (fun v : D ds => L₀ (e v)) := by
    simpa only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] using L.continuous
  obtain ⟨J, A, hA⟩ := isContinuousOnSmoothVectors_of_continuous I (R ds) L₀ hL₀
  let j : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let Xs : Fin (Fintype.card J) → List M := fun i => (j.symm i).val
  refine ⟨Fintype.card J, Xs, max A 0, le_max_right _ _, fun f c hc => ?_⟩
  have hNorm (i : Fin (Fintype.card J)) : ‖derivativeCLM I (R ds) (Xs i) (derivativeEquiv ds f)‖ ≤ c i := by
    have hci : 0 ≤ c i := (norm_nonneg _).trans (hc i 1 (unitaryCompact ℝ (r + 1)).one_mem)
    apply (ContinuousMap.norm_le _ hci).mpr
    intro k
    change ‖(derivativeCLM I (R ds) (Xs i) (derivativeEquiv ds f)).val k‖ ≤ c i
    rw [derivativeCLM_compactEval (r := r) ds]
    exact hc i (Unitary.toUnits k) k.property
  have hSem := hA (e (derivativeEquiv ds f))
  change ‖L₀ (e (derivativeEquiv ds f))‖ ≤ A *
    ∑ X ∈ J, ‖iteratedLieDerivative I (R ds) X (e (derivativeEquiv ds f))‖ at hSem
  simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe] at hSem
  simp only [e, ← derivativeCLM_apply] at hSem
  have hSum :
      (∑ X ∈ J, ‖derivativeCLM I (R ds) X (derivativeEquiv ds f)‖) =
        ∑ i, ‖derivativeCLM I (R ds) (Xs i) (derivativeEquiv ds f)‖ := by
    rw [← Finset.sum_coe_sort J]
    exact Fintype.sum_equiv j _ _ (fun x => by simp [Xs])
  exact hSem.trans <| (mul_le_mul_of_nonneg_right (le_max_left A 0)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans <| by
      rw [hSum]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hNorm i) (le_max_right _ _)

/-- Every smooth standard function lies in the smooth position principal series
of the expanded character list. -/
def expandedStandardInclusion (ds : List RealBlock) : (S ds) →ₗ[ℂ] P ds :=
  Submodule.inclusion fun _ hf => by
    have he : realPositionCharacter (RealPrincipalSeries.expand ds) =
        realPositionCharacter ds :=
      funext fun i => funext (RealPrincipalSeries.realPositionCharacter_expand ds i)
    rw [he]
    exact hf.1

/-- A continuous standard-module functional admits an extension with compact
derivative bound on the smooth expanded position model. -/
theorem exists_bound_extension (ds : List RealBlock) (L : (D ds) →L[ℂ] ℂ) :
    ∃ ℓ : (P ds) →ₗ[ℂ] ℂ, RealPrincipalSeries.HasCompactDerivativeBound r
        (RealPrincipalSeries.expand ds) ℓ ∧
      ∀ f : S ds, ℓ (expandedStandardInclusion ds f) = L (derivativeEquiv ds f) := by
  classical
  obtain ⟨m, Xs, A, hA, hb⟩ := has_compact_bound_of_continuous ds L
  let q₀ (i : Fin m) : Seminorm ℂ (P ds) :=
    (normSeminorm ℂ C(K, ℂ)).comp (RealPrincipalSeries.compactDerivativeCoordinate r ds (Xs i))
  let cA : NNReal := ⟨A, hA⟩
  let q : Seminorm ℂ (P ds) := cA • ∑ i, q₀ i
  have hq (p : P ds) : q p = A * ∑ i,
      ‖RealPrincipalSeries.compactDerivativeCoordinate r ds (Xs i) p‖ := by
    simp only [q, smul_apply, NNReal.smul_def, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      q₀, Seminorm.comp_apply, coe_normSeminorm]
    rfl
  let j := expandedStandardInclusion (r := r) ds
  have hj : Function.Injective j := fun _ _ h =>
    Subtype.ext (congrArg (fun p : P ds => p.val) h)
  let e := LinearEquiv.ofInjective j hj
  let L₀ : j.range →ₗ[ℂ] ℂ :=
    L.toLinearMap.comp ((derivativeEquiv ds).toLinearMap.comp e.symm.toLinearMap)
  have hL₀ (p : j.range) : ‖L₀ p‖ ≤ q p.val := by
    obtain ⟨f, rfl⟩ := e.surjective p
    change ‖L (derivativeEquiv ds (e.symm (e f)))‖ ≤ q (j f)
    rw [LinearEquiv.symm_apply_apply, hq]
    apply hb f (fun i => ‖RealPrincipalSeries.compactDerivativeCoordinate r ds (Xs i) (j f)‖)
    intro i k hk
    exact (RealPrincipalSeries.compactDerivativeCoordinate r ds (Xs i) (j f)).norm_coe_le_norm ⟨k, hk⟩
  obtain ⟨ℓ, hℓ, hℓq⟩ := Module.Dual.exists_extension_of_le_seminorm j.range L₀
    (p := q) hL₀
  refine ⟨ℓ, ⟨m, Xs, A, hA, ?_⟩, ?_⟩
  · intro p c hc
    refine (hℓq p).trans ?_
    rw [hq]
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hA
    have hci : 0 ≤ c i := (norm_nonneg _).trans (hc i 1 (unitaryCompact ℝ (r + 1)).one_mem)
    exact (ContinuousMap.norm_le _ hci).2 fun k => hc i k.val k.property
  · intro f
    have h := hℓ (e f)
    change ℓ (j f) = L (derivativeEquiv ds (e.symm (e f))) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h

/-- A compact-derivative-bounded functional on the expanded principal series
recovers every translated coefficient, given smooth Casselman–Wallach extension. -/
def RealWhittakerStandardEvaluationStatement : Prop :=
  RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0} →
    ∀ (m : ℕ) (ds : List RealBlock) (a : ℝˣ)
      (B : Automorphic.realStandardKFinite (m + 1) ds →ₗ[ℂ]
        (Langlands.GeneralLinear (m + 1) ℝ → ℂ)),
      IsIrreducibleGKModule (realStandardRep (m + 1) ds) (realStandardLie (m + 1) ds) →
      IsRealUniformWhittakerIntertwiner m ds a B →
        ∃ ℓ : principalSeries ℝ (m + 1)
            (realPositionCharacter (RealPrincipalSeries.expand ds)) →ₗ[ℂ] ℂ,
          RealPrincipalSeries.HasCompactDerivativeBound m (RealPrincipalSeries.expand ds) ℓ ∧
            ∀ f g, ℓ (RealPrincipalSeries.translate m (RealPrincipalSeries.expand ds) g
              (RealPrincipalSeries.expandedSmoothInclusion m ds f)) = B f g

theorem realWhittakerStandardEvaluation : RealWhittakerStandardEvaluationStatement := by
  intro hCW m ds a B hIrr hB
  obtain ⟨L, hL⟩ := exists_continuous_standardEvaluation hCW ds a B hIrr hB
  obtain ⟨ℓ, hBound, hℓ⟩ := exists_bound_extension ds L
  refine ⟨ℓ, hBound, fun f g => ?_⟩
  let f₀ : realStandardModule (m + 1) ds := ⟨f.val, f.property.1⟩
  have he : RealPrincipalSeries.translate m (RealPrincipalSeries.expand ds) g
        (RealPrincipalSeries.expandedSmoothInclusion m ds f) =
      expandedStandardInclusion ds (translate ds g f₀) :=
    Subtype.ext rfl
  rw [he, hℓ, derivativeEquiv_translate]
  exact hL f g

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
