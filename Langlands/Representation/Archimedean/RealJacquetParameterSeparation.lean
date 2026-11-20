import Langlands.Representation.Archimedean.GelfandParameterSeparation
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealSphericalCyclicProof

/-! # Infinitesimal-character separation for real Jacquet functionals -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.Archimedean.RealJacquetParameterSeparation

open RealCharacterCrossing (KF PL PL_position_exp PL_position_neg_one)
open RealJacquetFiniteGeneration (E D Mat op opMat op_E_commutator diagEval diagEval_X
  gen trace_gen_pow_mem_center envelopingAction_trace_gen_pow)
open GelfandParameterSeparation (value parameter_multiset_eq)
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ}

section Trace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Mat n) →ₗ⁅ℂ⁆ Module.End ℂ V)
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ}

private theorem diagEval_apply_functional
    (hd : ∀ i v, ℓ (op π (D i) v) = a i * ℓ v)
    (f : MvPolynomial (Fin n) ℂ) (v : V) :
    ℓ (diagEval π f v) = MvPolynomial.eval a f * ℓ v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, map_smul,
      MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, smul_eq_mul]
  | add f g hf hg => rw [map_add, LinearMap.add_apply, map_add, hf, hg, map_add, add_mul]
  | mul_X f i hf =>
    rw [mul_comm f (MvPolynomial.X i), map_mul, Module.End.mul_apply, diagEval_X, hd, hf,
      MvPolynomial.eval_mul, MvPolynomial.eval_X, mul_assoc]

private theorem trace_apply_functional
    (hu : ∀ i j : Fin n, i < j → ∀ v, ℓ (op π (E i j) v) = 0)
    (hd : ∀ i v, ℓ (op π (D i) v) = a i * ℓ v)
    (k : ℕ) (v : V) :
    ℓ (Matrix.trace (opMat π ^ k) v) =
      (∑ i, value (fun j => a j + (j.val : ℂ)) k i) * ℓ v := by
  have hgl : ComplexJacquetFinite.IsGlFamily (fun i j => op π (E i j)) := op_E_commutator π
  have hu' : ∀ i j : Fin n, i < j → ∀ w, op π (E i j) w ∈ LinearMap.ker ℓ :=
    fun i j h w => LinearMap.mem_ker.mpr (hu i j h w)
  have hd' : ∀ i w, w ∈ LinearMap.ker ℓ → op π (D i) w ∈ LinearMap.ker ℓ := by
    intro i w hw
    rw [LinearMap.mem_ker, hd, LinearMap.mem_ker.mp hw, mul_zero]
  rw [Matrix.trace, LinearMap.sum_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := ComplexJacquetFinite.diag_pow (LinearMap.ker ℓ) hgl hu' hd'
    (diagEval π) (diagEval_X π) k i v
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, diagEval_apply_functional π hd] at hi
  simpa only [Matrix.diag_apply, opMat, value, add_sub_cancel_right] using hi

private theorem strictUpper_E {i j : Fin n} (hij : i < j) :
    ∀ p q : Fin n, (q : ℕ) ≤ p → E i j p q = 0 := by
  intro p q hpq
  simp only [E, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (not_le_of_gt hij hpq).elim
  · rfl

/-- Nonzero real Jacquet functionals of the same infinitesimal-character module have the
same multiset of exponents after undoing the index shift. -/
theorem multiset_eq_of_jacquet {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    (hπ : HasInfinitesimalCharacter π) {ℓ' : V →ₗ[ℂ] ℂ} {a' : Fin n → ℂ}
    {e e' : Fin n → Fin 2} (h₀ : ℓ ≠ 0) (h₀' : ℓ' ≠ 0)
    (hℓ : IsRealJacquetFunctional n ρ π ℓ a e) (hℓ' : IsRealJacquetFunctional n ρ π ℓ' a' e') :
    (Finset.univ : Finset (Fin n)).val.map (fun i => a i + (i.val : ℂ)) =
      (Finset.univ : Finset (Fin n)).val.map (fun i => a' i + (i.val : ℂ)) := by
  apply parameter_multiset_eq
  intro k
  obtain ⟨c, hc⟩ := hπ _ (trace_gen_pow_mem_center n k)
  rw [envelopingAction_trace_gen_pow] at hc
  have htrace {L : V →ₗ[ℂ] ℂ} {b : Fin n → ℂ} {s : Fin n → Fin 2}
      (hL₀ : L ≠ 0) (hL : IsRealJacquetFunctional n ρ π L b s) :
      (∑ i, value (fun j => b j + (j.val : ℂ)) k i) = c := by
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra! hn
      exact hL₀ (LinearMap.ext (by simpa using hn))
    apply mul_right_cancel₀ hv
    rw [← trace_apply_functional π (fun i j h w => hL.1 (E i j) (strictUpper_E h) w)
      (fun i w => (hL.2 i w).1) k v, hc, Module.algebraMap_end_apply, map_smul, smul_eq_mul]
  rw [htrace h₀ hℓ, htrace h₀' hℓ']

end Trace

/-- The diagonal infinitesimal exponents of a normalized real principal series. -/
def diagonalExponent (τ : Fin n → ℂ) (i : Fin n) : ℂ :=
  τ i + ((n : ℂ) - 1) / 2 - (i.val : ℂ)

/-- Evaluation at the identity on the finite vectors of a real principal series. -/
abbrev evalOne (ds : List RealBlock) : KF n ds →ₗ[ℂ] ℂ :=
  kFiniteEval (realStandardModule n ds) 1

private theorem evalOne_lie_upper (τ : Fin n → ℂ) (e : Fin n → Fin 2)
    (X : Mat n) (hX : X.IsUpperTriangular) (v : KF n (PL τ e)) :
    evalOne (PL τ e) (realStandardLie n (PL τ e) (1 ⊗ₜ X) v) =
      (∑ i, diagonalExponent τ i * (X i i : ℂ)) * evalOne (PL τ e) v := by
  have hv := (realStandardModule_le_principalSeries n (PL τ e)) v.2.1
  have hv' := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries (PL_position_exp τ e) hv
  have h := RealBlockDerivative.fderiv_upperTriangular_of_isExpEquivariant hv.1 hv' 1 hX
  simp only [Units.val_one, mul_one] at h
  simp only [evalOne, kFiniteEval_apply, realStandardLie_one_tmul_apply_coe,
    rightDerivative_eq_fderiv hv.1, Units.val_one, one_mul]
  exact h

/-- Evaluation at the identity has the diagonal exponents and signs of the inducing data. -/
theorem evalOne_isJacquet (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    IsRealJacquetFunctional n (realStandardRep n (PL τ e)) (realStandardLie n (PL τ e))
      (evalOne (PL τ e)) (diagonalExponent τ) e := by
  constructor
  · intro X hX v
    have hup : X.IsUpperTriangular := fun i j h => hX i j h.le
    rw [evalOne_lie_upper τ e X hup]
    simp [fun i => hX i i le_rfl]
  · intro i v
    constructor
    · have hup : (D i).IsUpperTriangular := by
        intro j k hjk
        simp only [D, E, Matrix.single_apply]
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h
          exact (lt_irrefl _ hjk).elim
        · rfl
      rw [evalOne_lie_upper τ e (D i) hup]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp [D, E]
      · intro j _ hj
        simp [D, E, hj.symm]
      · simp
    · have hv := (realStandardModule_le_principalSeries n (PL τ e)) v.2.1
      have hone := RealSphericalCyclicProof.realPositionCharacter_map_one
        (List.ofFn fun i => RealJacquetFrobenius.charData (e i) (τ i))
      simp only [evalOne, kFiniteEval_apply, realStandardRep_apply_coe,
        TranslateFinite.rightTranslation_apply, one_mul]
      have hsign := RealBlockFourierFinite.apply_signReflection_mul hone hv i 1
      change _ = realPositionCharacter (PL τ e) i (-1) * _ at hsign
      simpa only [mul_one, PL_position_neg_one] using hsign

/-- The sign monomial on the compact group extends to a finite principal-series vector. -/
theorem exists_signMonomial_extension (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    ∃ v : KF n (PL τ e), ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
      (v : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) =
        JacquetNonvanishing.signMonomial n (RealCharacterCrossing.pE e) 0 k := by
  open RealCharacterCrossing JacquetNonvanishing in
  obtain ⟨f, hf, hfK⟩ := principalSeriesExtension n (PL τ e) (signMonomial n (pE e) 0)
    (continuous_signMonomial _ _) (finiteDimensional_signMonomial _ _)
    (signMonomial_signDiagonal (pE e) 0 (PL_position_neg_one_pE τ e)
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _))
  exact ⟨⟨f, RealCharacterCrossing.mem_KF_of_mem τ e hf⟩, hfK⟩

/-- Evaluation is nonzero in every signed real principal series. -/
theorem evalOne_ne_zero (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    evalOne (n := n) (PL τ e) ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_signMonomial_extension τ e
  have h := hv 1
  rw [map_one] at h
  have hv1 : evalOne (PL τ e) v = 1 := by
    change (v : Langlands.GeneralLinear n ℝ → ℂ) 1 = 1
    rw [h]
    simp [JacquetNonvanishing.signMonomial]
  intro hzero
  rw [hzero, LinearMap.zero_apply] at hv1
  exact zero_ne_one hv1

/-- A nonzero Jacquet functional on a principal series has, after normalization, the
multiset of exponents of the inducing characters. -/
theorem multiset_eq_of_principal {τ : Fin n → ℂ} {e : Fin n → Fin 2}
    {ℓ : KF n (PL τ e) →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {s : Fin n → Fin 2}
    (h₀ : ℓ ≠ 0)
    (hℓ : IsRealJacquetFunctional n (realStandardRep n (PL τ e)) (realStandardLie n (PL τ e)) ℓ a s) :
    (Finset.univ : Finset (Fin n)).val.map (RealJacquetFrobenius.expo a) =
      (Finset.univ : Finset (Fin n)).val.map τ := by
  have h := multiset_eq_of_jacquet (realStandardLie n (PL τ e))
    (realStandardLie_hasInfinitesimalCharacter n (PL τ e))
    h₀ (evalOne_ne_zero τ e) hℓ (evalOne_isJacquet τ e)
  have h' := congrArg (Multiset.map (fun z : ℂ => z - ((n : ℂ) - 1) / 2)) h
  simp only [Multiset.map_map, Function.comp_def] at h'
  have hleft : (fun i => a i + (i.val : ℂ) - ((n : ℂ) - 1) / 2) =
      RealJacquetFrobenius.expo a := by
    funext i
    simp only [RealJacquetFrobenius.expo]
    ring
  have hright : (fun i => diagonalExponent τ i + (i.val : ℂ) - ((n : ℂ) - 1) / 2) = τ := by
    funext i
    simp only [diagonalExponent]
    ring
  rw [hleft, hright] at h'
  exact h'

/-- Evaluation on all compact translates detects a vector of a real standard module. -/
theorem eq_zero_of_evalOne_rep {ds : List RealBlock} {v : KF n ds}
    (h : ∀ k, evalOne ds (realStandardRep n ds k v) = 0) : v = 0 :=
  RealTemperedCommutantReduction.eq_zero_of_compact_eval n ds v h

end Langlands.Archimedean.RealJacquetParameterSeparation
