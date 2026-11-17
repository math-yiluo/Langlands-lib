import Langlands.Global.RankinSelberg.SchwartzCoordinateMajorant
import Langlands.Global.RankinSelberg.SchwartzBruhat
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Schwartz--Bruhat majorants from archimedean decay and finite support -/

noncomputable section
universe u
open NumberField
open scoped Classical ContDiff RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzMajorant

variable (F : Type u) [Field F] [NumberField F]

local instance : T2Space (FiniteAdeles F) :=
  inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
    [FiniteCompletion F v, v.adicCompletionIntegers F]))

/-- Finite rows with the common rational denominator `c`. -/
def denominatorRows (r : ℕ) (c : F) : Set (Fin r → FiniteAdeles F) :=
  {y | ∀ i, algebraMap F (FiniteAdeles F) c * y i ∈ integralFiniteAdeles F}

theorem denominatorRows_isClopen (r : ℕ) (c : F) :
    IsClopen (denominatorRows F r c) := by
  have heq : denominatorRows F r c = ⋂ i : Fin r,
      {y | algebraMap F (FiniteAdeles F) c * y i ∈ integralFiniteAdeles F} := by
    ext y
    simp only [denominatorRows, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  constructor
  · exact isClosed_iInter fun i => (isCompact_integralFiniteAdeles F).isClosed.preimage
      (continuous_const.mul (continuous_apply i))
  · exact isOpen_iInter_of_finite fun i => (isOpen_integralFiniteAdeles F).preimage
      (continuous_const.mul (continuous_apply i))

theorem denominatorRows_isCompact (r : ℕ) {c : F} (hc : c ≠ 0) :
    IsCompact (denominatorRows F r c) := by
  have heq : denominatorRows F r c =
      (fun y : Fin r → FiniteAdeles F =>
        fun i => algebraMap F (FiniteAdeles F) c⁻¹ * y i) ''
        Set.pi Set.univ (fun _ : Fin r =>
          (integralFiniteAdeles F : Set (FiniteAdeles F))) := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i => algebraMap F (FiniteAdeles F) c * y i, ?_, ?_⟩
      · exact fun i _ => hy i
      · funext i
        dsimp only
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    · rintro ⟨z, hz, rfl⟩ i
      dsimp only
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
      exact hz i (Set.mem_univ i)
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles F).image
    (continuous_pi fun i => continuous_const.mul (continuous_apply i))

/-- A compactly supported locally constant cutoff for the denominator rows. -/
def denominatorCutoff (r : ℕ) (c : F) :
    LocallyConstant (Fin r → FiniteAdeles F) ℂ :=
  LocallyConstant.charFn ℂ (denominatorRows_isClopen F r c)

theorem denominatorCutoff_hasCompactSupport (r : ℕ) {c : F} (hc : c ≠ 0) :
    HasCompactSupport (denominatorCutoff F r c) := by
  apply (denominatorRows_isCompact F r hc).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro y hy
    by_contra h
    exact hy ((LocallyConstant.charFn_eq_zero ℂ y _).mpr h)
  · exact (denominatorRows_isClopen F r c).1

theorem denominatorCutoff_eq_of_mem_iff (r : ℕ) (c : F)
    (x y : Fin r → FiniteAdeles F)
    (hxy : ∀ i, (algebraMap F (FiniteAdeles F) c * x i ∈ integralFiniteAdeles F ↔
      algebraMap F (FiniteAdeles F) c * y i ∈ integralFiniteAdeles F)) :
    denominatorCutoff F r c x = denominatorCutoff F r c y := by
  have hmem : x ∈ denominatorRows F r c ↔ y ∈ denominatorRows F r c :=
    forall_congr' hxy
  simp only [denominatorCutoff, LocallyConstant.coe_charFn, Set.indicator_apply,
    Pi.one_apply, hmem]

/-- Uniform archimedean rapid decay and a common finite denominator give
a Schwartz--Bruhat majorant, with local-magnitude symmetries retained. -/
theorem exists_schwartzBruhat_majorant {r : ℕ} {J : Type*}
    (z : J → RowVector F r) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hrapid : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (1 + ‖archimedeanCoordinates F r (z j)‖) ^ N * w j ≤ C)
    (c : F) (hc : c ≠ 0)
    (hsupp : ∀ j, w j ≠ 0 → finiteCoordinates F r (z j) ∈ denominatorRows F r c) :
    ∃ Φ : RowVector F r → ℂ, Φ ∈ schwartzBruhat F r ∧
      (∀ j, w j ≤ ‖Φ (z j)‖) ∧
      ∀ x y,
        (∀ i a, ‖(archimedeanCoordinates F r x i).1 a‖ =
          ‖(archimedeanCoordinates F r y i).1 a‖) →
        (∀ i b, ‖(archimedeanCoordinates F r x i).2 b‖ =
          ‖(archimedeanCoordinates F r y i).2 b‖) →
        (∀ i, (algebraMap F (FiniteAdeles F) c * finiteCoordinates F r x i ∈
            integralFiniteAdeles F ↔
          algebraMap F (FiniteAdeles F) c * finiteCoordinates F r y i ∈
            integralFiniteAdeles F)) → Φ x = Φ y := by
  obtain ⟨φ, hφnon, hφbound, hφeq⟩ := exists_coordinate_schwartz_majorant
    (fun j => archimedeanCoordinates F r (z j)) w hw hrapid
  let φc := φ.postcompCLM Complex.ofRealCLM
  let Φ : RowVector F r → ℂ := fun x =>
    φc (archimedeanCoordinates F r x) * denominatorCutoff F r c (finiteCoordinates F r x)
  refine ⟨Φ, Submodule.subset_span ?_, ?_, ?_⟩
  · exact ⟨φc, denominatorCutoff F r c,
      (denominatorCutoff F r c).isLocallyConstant, denominatorCutoff_hasCompactSupport F r hc,
      rfl⟩
  · intro j
    by_cases hj : w j = 0
    · rw [hj]
      exact norm_nonneg _
    · have hcut : denominatorCutoff F r c (finiteCoordinates F r (z j)) = 1 :=
        (LocallyConstant.charFn_eq_one ℂ _ _).mpr (hsupp j hj)
      simpa only [Φ, hcut, mul_one, φc, SchwartzMap.postcompCLM_apply,
        Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_of_nonneg (hφnon _)]
        using hφbound j
  · intro x y hr hcc hf
    dsimp only [Φ]
    rw [denominatorCutoff_eq_of_mem_iff F r c _ _ hf]
    congr 1
    change (φ (archimedeanCoordinates F r x) : ℂ) =
      (φ (archimedeanCoordinates F r y) : ℂ)
    rw [hφeq _ _ hr hcc]

end Langlands.Global.RankinSelbergGlobal.SchwartzMajorant
