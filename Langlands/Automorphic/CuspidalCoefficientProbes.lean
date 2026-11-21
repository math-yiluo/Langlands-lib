import Langlands.Automorphic.CuspidalStandardTensorEvaluation
import Langlands.Representation.Archimedean.ComplexSwapJacquetLie
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.RealSubquotientEval
import Langlands.Representation.Tensor.ProductFunctionals

/-! # Algebraic coefficient probes of cuspidal block tensors -/

noncomputable section

open scoped BigOperators TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.FiniteTensor Langlands.Global
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

private def contractEquiv {V M W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup W] [Module ℂ W]
    (e : V ⊗[ℂ] M ≃ₗ[ℂ] W) (μ : Module.Dual ℂ M) : W →ₗ[ℂ] V :=
  (contractRight μ).comp e.symm.toLinearMap

private theorem contractEquiv_intertwines {V M W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup W] [Module ℂ W]
    (e : V ⊗[ℂ] M ≃ₗ[ℂ] W) (μ : Module.Dual ℂ M)
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (h : ∀ t, e (TensorProduct.map A LinearMap.id t) = B (e t)) (x : W) :
    contractEquiv e μ (B x) = A (contractEquiv e μ x) := by
  have hx : e.symm (B x) = TensorProduct.map A LinearMap.id (e.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, h, e.apply_symm_apply]
  change contractRight μ (e.symm (B x)) = A (contractRight μ (e.symm x))
  rw [hx, contractRight_map]

section Probes

variable {ι : Type*} [Fintype ι] {V M W : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private def coefficientProbe (e : ∀ i, V i ⊗[ℂ] M i ≃ₗ[ℂ] W i)
    (ev : ∀ i, Module.Dual ℂ (V i)) (μ : ∀ i, Module.Dual ℂ (M i)) :
    Module.Dual ℂ (⨂[ℂ] i, W i) :=
  productFunctional fun i => (ev i).comp (contractEquiv (e i) (μ i))

private theorem exists_coefficientProbe_slice [DecidableEq ι]
    (e : ∀ i, V i ⊗[ℂ] M i ≃ₗ[ℂ] W i) (ev : ∀ i, Module.Dual ℂ (V i))
    (μ : ∀ i, Module.Dual ℂ (M i)) (i : ι) (z : ⨂[ℂ] i, W i) :
    ∃ f : V i, coefficientProbe e ev μ z = ev i f ∧
      ∀ (A : Module.End ℂ (V i)) (B : Module.End ℂ (W i)),
        (∀ t, e i (TensorProduct.map A LinearMap.id t) = B (e i t)) →
        coefficientProbe e ev μ
            (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i B) z) =
          ev i (A f) := by
  let ℓ (j : ι) := (ev j).comp (contractEquiv (e j) (μ j))
  obtain ⟨x, hx⟩ := exists_productFunctional_slice ℓ i z
  refine ⟨contractEquiv (e i) (μ i) x, ?_, fun A B h => ?_⟩
  · simpa only [coefficientProbe, ℓ, Function.update_eq_self, PiTensorProduct.map_id,
      LinearMap.id_apply, LinearMap.comp_apply] using hx LinearMap.id
  · change productFunctional ℓ _ = _
    rw [hx B, LinearMap.comp_apply, contractEquiv_intertwines _ _ A B h]

private theorem coefficientProbe_separates
    {K : ι → Type*}
    (e : ∀ i, V i ⊗[ℂ] M i ≃ₗ[ℂ] W i) (ev : ∀ i, Module.Dual ℂ (V i))
    (ρ : ∀ i, K i → Module.End ℂ (V i)) (κ : ∀ i, K i → Module.End ℂ (W i))
    (hK : ∀ i k t, e i (TensorProduct.map (ρ i k) LinearMap.id t) = κ i k (e i t))
    (hsep : ∀ i f, (∀ k, ev i (ρ i k f) = 0) → f = 0)
    (z : ⨂[ℂ] i, W i)
    (hz : ∀ μ (k : ∀ i, K i),
      coefficientProbe e ev μ (PiTensorProduct.map (fun i => κ i (k i)) z) = 0) :
    z = 0 := by
  let test (i : ι) (p : Module.Dual ℂ (M i) × K i) :=
    ((ev i).comp (contractEquiv (e i) p.1)).comp (κ i p.2)
  have htest (i : ι) (x : W i) (hx : ∀ p, test i p x = 0) : x = 0 := by
    have he : (e i).symm x = 0 := by
      apply eq_zero_of_contractRight
      intro μ
      apply hsep i
      intro k
      have hk := hx (μ, k)
      change ev i (contractEquiv (e i) μ (κ i k x)) = 0 at hk
      rw [contractEquiv_intertwines _ _ _ _ (hK i k)] at hk
      exact hk
    apply (e i).symm.injective
    rwa [map_zero]
  refine productFunctional_separates test htest z (fun p => ?_)
  exact (productFunctional_map (fun i => (ev i).comp (contractEquiv (e i) (p i).1))
    (fun i => κ i (p i).2) z).symm.trans (hz (fun i => (p i).1) (fun i => (p i).2))

end Probes

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable {r : ℕ} (S : CuspidalOperatorRealization F r)

/-- The algebraic multiplicity space of a real standard module in a cuspidal block. -/
abbrev realStandardMultiplicity (v : {w : NumberField.InfinitePlace F // w.IsReal})
    (ds : List RealBlock) :=
  GKTensorEvaluation.Multiplicity (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)
    (S.realization.realPlaceCompactRepresentation v) (S.realization.realPlaceLieAction v)

/-- The algebraic multiplicity space of a complex standard module in a cuspidal block. -/
abbrev complexStandardMultiplicity (v : {w : NumberField.InfinitePlace F // w.IsComplex})
    (ds : List ComplexCharacterData) :=
  GKTensorEvaluation.Multiplicity (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)
    (S.realization.complexPlaceCompactRepresentation v) (S.realization.complexPlaceLieAction v)

variable {c : ℕ} {m : Fin c → ℕ} (T : ∀ i, CuspidalOperatorRealization F (m i))

section Real

variable (v : {w : NumberField.InfinitePlace F // w.IsReal}) (ds : Fin c → List RealBlock)
  (hp : ∀ i, (T i).realization.HasRealPlaceParameter v (ds i))

private def realCoefficientEvaluation (i : Fin c) :
    realStandardKFinite (m i + 1) (ds i) ⊗[ℂ] (T i).realStandardMultiplicity v (ds i) ≃ₗ[ℂ]
      (T i).Space :=
  LinearEquiv.ofBijective (GKTensorEvaluation.evaluation _ _ _ _)
    ((T i).standardTensorEvaluation.1 v (ds i) (hp i))

/-- Take the product of the evaluations at the identity of the real standard factors
after contracting against the supplied block multiplicity functionals. -/
def realCoefficientProbe (μ : ∀ i, Module.Dual ℂ ((T i).realStandardMultiplicity v (ds i))) :
    Module.Dual ℂ (⨂[ℂ] i, (T i).Space) :=
  coefficientProbe (realCoefficientEvaluation T v ds hp)
    (fun i => kFiniteEval (realStandardModule (m i + 1) (ds i)) 1) μ

set_option maxHeartbeats 600000 in
/-- On one real block the compact and Lie coefficients are given by one vector of
that block's standard module. -/
theorem realCoefficientProbe_slice
    (μ : ∀ i, Module.Dual ℂ ((T i).realStandardMultiplicity v (ds i))) (i : Fin c)
    (z : ⨂[ℂ] i, (T i).Space) :
    ∃ f : realStandardKFinite (m i + 1) (ds i),
      realCoefficientProbe T v ds hp μ z = f.val 1 ∧
      (∀ k : Matrix.unitaryGroup (Fin (m i + 1)) ℝ,
        realCoefficientProbe T v ds hp μ (PiTensorProduct.map (Function.update
          (fun _ => LinearMap.id) i ((T i).realization.realPlaceCompactRepresentation v k)) z) =
          f.val (Unitary.toUnits k)) ∧
      ∀ X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℝ,
        realCoefficientProbe T v ds hp μ (PiTensorProduct.map (Function.update
          (fun _ => LinearMap.id) i ((T i).realization.realPlaceLieAction v (1 ⊗ₜ X))) z) =
          (realStandardLie (m i + 1) (ds i) (1 ⊗ₜ X) f).val 1 := by
  refine (exists_coefficientProbe_slice
    (V := fun j => ↥(realStandardKFinite (m j + 1) (ds j)))
    (M := fun j => ↥((T j).realStandardMultiplicity v (ds j)))
    (W := fun j => ↥((T j).Space)) (realCoefficientEvaluation T v ds hp)
    (fun j => kFiniteEval (realStandardModule (m j + 1) (ds j)) 1) μ i z).imp ?_
  intro f h
  refine ⟨h.1, fun k => ?_, fun X => ?_⟩
  · have hK := GKTensorEvaluation.evaluation_compact
      (realStandardRep (m i + 1) (ds i)) (realStandardLie (m i + 1) (ds i))
      ((T i).realization.realPlaceCompactRepresentation v) ((T i).realization.realPlaceLieAction v) k
    have h := h.2 (realStandardRep (m i + 1) (ds i) k)
      ((T i).realization.realPlaceCompactRepresentation v k) hK
    change realCoefficientProbe T v ds hp μ _ =
      ((realStandardRep (m i + 1) (ds i) k f : realStandardKFinite (m i + 1) (ds i)) :
        Langlands.GeneralLinear (m i + 1) ℝ → ℂ) 1 at h
    simpa only [realStandardRep_apply_coe, TranslateFinite.rightTranslation_apply, one_mul] using h
  · have hL := GKTensorEvaluation.evaluation_lie
      (realStandardRep (m i + 1) (ds i)) (realStandardLie (m i + 1) (ds i))
      ((T i).realization.realPlaceCompactRepresentation v) ((T i).realization.realPlaceLieAction v) (1 ⊗ₜ X)
    exact h.2 (realStandardLie (m i + 1) (ds i) (1 ⊗ₜ X))
      ((T i).realization.realPlaceLieAction v (1 ⊗ₜ X)) hL

set_option maxHeartbeats 600000 in
/-- The real probes satisfy the upper Borel Jacquet equations in each block. -/
theorem realCoefficientProbe_jacquet
    (μ : ∀ i, Module.Dual ℂ ((T i).realStandardMultiplicity v (ds i))) (i : Fin c)
    (z : ⨂[ℂ] i, (T i).Space) :
    let ℓ := realCoefficientProbe T v ds hp μ
    let d (X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℝ) :=
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
        ((T i).realization.realPlaceLieAction v (1 ⊗ₜ X)))
    let s (j : Fin (m i + 1)) :=
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
        ((T i).realization.realPlaceCompactRepresentation v (signReflection (m i + 1) j)))
    (∀ X, (∀ a b : Fin (m i + 1), b ≤ a → X a b = 0) → ℓ (d X z) = 0) ∧
      ∀ j : Fin (m i + 1),
        ℓ (d (Matrix.single j j 1) z) =
          RealBlockPosition.shiftedExponent (m i + 1) (ds i) j * ℓ z ∧
        ℓ (s j z) = (-1) ^ (RealBlockPosition.positionSign (m i + 1) (ds i) j).val * ℓ z := by
  dsimp only
  refine (realCoefficientProbe_slice T v ds hp μ i z).elim ?_
  intro f h
  have hps := f.property.1.1
  rw [← RealBlockPosition.principalSeries_posChar_shiftedExponent] at hps
  refine ⟨fun X hX => ?_, fun j => ⟨?_, ?_⟩⟩
  · have hu : X.IsUpperTriangular := fun _ _ h => hX _ _ h.le
    refine (h.2.2 X).trans ?_
    rw [realStandardLie_one_tmul_apply_coe, RealSubquotient.rightDerivative_upper_apply_one hps hu]
    have hd (j : Fin (m i + 1)) : X j j = 0 := hX j j le_rfl
    simp [hd]
  · have hu : (Matrix.single j j (1 : ℝ)).IsUpperTriangular :=
      Matrix.blockTriangular_single (b := id) le_rfl 1
    refine (h.2.2 (Matrix.single j j 1)).trans ?_
    rw [realStandardLie_one_tmul_apply_coe, RealSubquotient.rightDerivative_upper_apply_one hps hu,
      h.1]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  · rw [h.2.1, h.1]
    simpa only [mul_one, RealBlockPosition.realPositionCharacter_neg_one,
      RealBlockPosition.positionSign] using
      RealBlockFourierFinite.apply_signReflection_mul (RealLeviSlices.realPositionCharacter_one (ds i))
        f.property.1.1 j 1

set_option synthInstance.maxHeartbeats 80000 in
/-- The real probes after product-compact translation separate the cuspidal block tensor. -/
theorem realCoefficientProbe_separates (z : ⨂[ℂ] i, (T i).Space)
    (hz : ∀ μ (k : ∀ i, Matrix.unitaryGroup (Fin (m i + 1)) ℝ),
      realCoefficientProbe T v ds hp μ (PiTensorProduct.map
        (fun i => (T i).realization.realPlaceCompactRepresentation v (k i)) z) = 0) :
    z = 0 := by
  refine coefficientProbe_separates (realCoefficientEvaluation T v ds hp)
    (fun i => kFiniteEval (realStandardModule (m i + 1) (ds i)) 1)
    (fun i k => realStandardRep (m i + 1) (ds i) k)
    (fun i k => (T i).realization.realPlaceCompactRepresentation v k)
    (fun _ k => GKTensorEvaluation.evaluation_compact _ _ _ _ k) ?_ z hz
  intro i f hf
  apply Subtype.ext
  apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.property.1.1
  intro k hk
  let k' : Matrix.unitaryGroup (Fin (m i + 1)) ℝ := ⟨k.val, hk⟩
  have h : Unitary.toUnits k' = k := Units.ext rfl
  simpa only [kFiniteEval_apply, realStandardRep_apply_coe, TranslateFinite.rightTranslation_apply,
    one_mul, h] using hf k'

end Real

section Complex

variable (v : {w : NumberField.InfinitePlace F // w.IsComplex})
  (ds : Fin c → List ComplexCharacterData)
  (hp : ∀ i, (T i).realization.HasComplexPlaceParameter v (ds i))

private def complexCoefficientEvaluation (i : Fin c) :
    complexStandardKFinite (m i + 1) (ds i) ⊗[ℂ] (T i).complexStandardMultiplicity v (ds i) ≃ₗ[ℂ]
      (T i).Space :=
  LinearEquiv.ofBijective (GKTensorEvaluation.evaluation _ _ _ _)
    ((T i).standardTensorEvaluation.2 v (ds i) (hp i))

/-- The analogous product of evaluations at the identity for the complex standard factors. -/
def complexCoefficientProbe (μ : ∀ i, Module.Dual ℂ ((T i).complexStandardMultiplicity v (ds i))) :
    Module.Dual ℂ (⨂[ℂ] i, (T i).Space) :=
  coefficientProbe (complexCoefficientEvaluation T v ds hp)
    (fun i => kFiniteEval (complexStandardModule (m i + 1) (ds i)) 1) μ

set_option maxHeartbeats 600000 in
/-- The compact and Lie coefficients in a complex slot come from one standard-module
vector, with differentiation along the real directions of the complex Lie algebra. -/
theorem complexCoefficientProbe_slice
    (μ : ∀ i, Module.Dual ℂ ((T i).complexStandardMultiplicity v (ds i))) (i : Fin c)
    (z : ⨂[ℂ] i, (T i).Space) :
    ∃ f : complexStandardKFinite (m i + 1) (ds i),
      complexCoefficientProbe T v ds hp μ z = f.val 1 ∧
      (∀ k : Matrix.unitaryGroup (Fin (m i + 1)) ℂ,
        complexCoefficientProbe T v ds hp μ (PiTensorProduct.map (Function.update
          (fun _ => LinearMap.id) i ((T i).realization.complexPlaceCompactRepresentation v k)) z) =
          f.val (Unitary.toUnits k)) ∧
      ∀ X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℂ,
        complexCoefficientProbe T v ds hp μ (PiTensorProduct.map (Function.update
          (fun _ => LinearMap.id) i ((T i).realization.complexPlaceLieAction v (1 ⊗ₜ X))) z) =
          (complexStandardLie (m i + 1) (ds i) (1 ⊗ₜ X) f).val 1 := by
  refine (exists_coefficientProbe_slice
    (V := fun j => ↥(complexStandardKFinite (m j + 1) (ds j)))
    (M := fun j => ↥((T j).complexStandardMultiplicity v (ds j)))
    (W := fun j => ↥((T j).Space)) (complexCoefficientEvaluation T v ds hp)
    (fun j => kFiniteEval (complexStandardModule (m j + 1) (ds j)) 1) μ i z).imp ?_
  intro f h
  refine ⟨h.1, fun k => ?_, fun X => ?_⟩
  · have hK := GKTensorEvaluation.evaluation_compact
      (complexStandardRep (m i + 1) (ds i)) (complexStandardLie (m i + 1) (ds i))
      ((T i).realization.complexPlaceCompactRepresentation v) ((T i).realization.complexPlaceLieAction v) k
    have h := h.2 (complexStandardRep (m i + 1) (ds i) k)
      ((T i).realization.complexPlaceCompactRepresentation v k) hK
    change complexCoefficientProbe T v ds hp μ _ =
      ((complexStandardRep (m i + 1) (ds i) k f : complexStandardKFinite (m i + 1) (ds i)) :
        Langlands.GeneralLinear (m i + 1) ℂ → ℂ) 1 at h
    simpa only [principalSeriesRep_apply_coe, TranslateFinite.rightTranslation_apply, one_mul] using h
  · have hL := GKTensorEvaluation.evaluation_lie
      (complexStandardRep (m i + 1) (ds i)) (complexStandardLie (m i + 1) (ds i))
      ((T i).realization.complexPlaceCompactRepresentation v)
      ((T i).realization.complexPlaceLieAction v) (1 ⊗ₜ X)
    exact h.2 (complexStandardLie (m i + 1) (ds i) (1 ⊗ₜ X))
      ((T i).realization.complexPlaceLieAction v (1 ⊗ₜ X)) hL

set_option maxHeartbeats 600000 in
/-- The complex probes satisfy the upper Borel Jacquet equations in each block,
including for both real and imaginary diagonal directions. -/
theorem complexCoefficientProbe_jacquet
    (μ : ∀ i, Module.Dual ℂ ((T i).complexStandardMultiplicity v (ds i))) (i : Fin c)
    (z : ⨂[ℂ] i, (T i).Space) :
    let ℓ := complexCoefficientProbe T v ds hp μ
    let d (X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℂ) :=
      PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i
        ((T i).realization.complexPlaceLieAction v (1 ⊗ₜ X)))
    (∀ X, (∀ a b : Fin (m i + 1), b ≤ a → X a b = 0) → ℓ (d X z) = 0) ∧
      ∀ (j : Fin (m i + 1)) (a : ℂ),
        ℓ (d (Matrix.single j j a) z) = ComplexSwapJacquet.kappa (ds i) (hp i).1 j a * ℓ z := by
  dsimp only
  refine (complexCoefficientProbe_slice T v ds hp μ i z).elim ?_
  intro f h
  have hdiff (X : Matrix (Fin (m i + 1)) (Fin (m i + 1)) ℂ) :=
    congrFun (principalSeriesLie_one_tmul_apply_coe ℂ (m i + 1)
      (complexPositionCharacter (ds i)) X f) 1
  refine ⟨fun X hX => ?_, fun j a => ?_⟩
  · exact (h.2.2 X).trans ((hdiff X).trans
      (ComplexSwapJacquet.rightDerivative_one_strictUpper f.property.1 X hX))
  · refine (h.2.2 _).trans ((hdiff _).trans
      ((ComplexSwapJacquet.rightDerivative_one_diag (hp i).1 f.property.1 j a).trans ?_))
    exact congrArg (ComplexSwapJacquet.kappa (ds i) (hp i).1 j a * ·) h.1.symm

set_option synthInstance.maxHeartbeats 80000 in
/-- The complex probes after product-compact translation separate the cuspidal block tensor. -/
theorem complexCoefficientProbe_separates (z : ⨂[ℂ] i, (T i).Space)
    (hz : ∀ μ (k : ∀ i, Matrix.unitaryGroup (Fin (m i + 1)) ℂ),
      complexCoefficientProbe T v ds hp μ (PiTensorProduct.map
        (fun i => (T i).realization.complexPlaceCompactRepresentation v (k i)) z) = 0) :
    z = 0 := by
  refine coefficientProbe_separates (complexCoefficientEvaluation T v ds hp)
    (fun i => kFiniteEval (complexStandardModule (m i + 1) (ds i)) 1)
    (fun i k => complexStandardRep (m i + 1) (ds i) k)
    (fun i k => (T i).realization.complexPlaceCompactRepresentation v k)
    (fun _ k => GKTensorEvaluation.evaluation_compact _ _ _ _ k) ?_ z hz
  intro i f hf
  apply Subtype.ext
  apply PrincipalSeries.eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.property.1
  intro k hk
  let k' : Matrix.unitaryGroup (Fin (m i + 1)) ℂ := ⟨k.val, hk⟩
  have h : Unitary.toUnits k' = k := Units.ext rfl
  simpa only [kFiniteEval_apply, principalSeriesRep_apply_coe, TranslateFinite.rightTranslation_apply,
    one_mul, h] using hf k'

end Complex

end CuspidalOperatorRealization
end Langlands.Automorphic
