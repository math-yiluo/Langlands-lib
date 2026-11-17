import Langlands.Analysis.NonarchimedeanCompletedTensorProof
import Langlands.Geometry.Analytic.CompletedTensorAlgebra
import Mathlib.Order.WellFounded

/-! # Separated tensor completion over complete ultrametric fields -/

noncomputable section

universe u v w

open scoped TensorProduct NNReal

namespace Langlands.Analytic.SeparatedFieldTensor

open UltrametricTensorSeminorm
open Langlands.Analysis.NonarchimedeanCompletedTensorProof

private def normBall {F V : Type*} [NormedField F] [NormedAddCommGroup V]
    [NormedSpace F V] [IsUltrametricDist V] (htriv : ∀ c : F, ‖c‖ ≤ 1)
    (r : {r : ℝ // 0 < r}) : Submodule F V where
  carrier := {v | ‖v‖ < r.1}
  zero_mem' := by simpa using r.2
  add_mem' hv hw := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hv hw)
  smul_mem' c v hv := (norm_smul_le c v).trans_lt
    ((mul_le_mul_of_nonneg_right (htriv c) (norm_nonneg v)).trans_lt (by simpa using hv))

private theorem norm_lower_bound {F V : Type*} [NormedField F]
    [NormedAddCommGroup V] [NormedSpace F V] [IsUltrametricDist V]
    [FiniteDimensional F V] (htriv : ∀ c : F, ‖c‖ ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : V, v ≠ 0 → ε ≤ ‖v‖ := by
  let : Nonempty {r : ℝ // 0 < r} := ⟨⟨1, one_pos⟩⟩
  let d (r : {r : ℝ // 0 < r}) := Module.finrank F (normBall (V := V) htriv r)
  let r := Function.argmin d
  refine ⟨r.1, r.2, fun v hv => le_of_not_gt fun hvr => ?_⟩
  let s : {r : ℝ // 0 < r} := ⟨min r.1 ‖v‖, lt_min r.2 (norm_pos_iff.mpr hv)⟩
  have heq : normBall (V := V) htriv s = normBall htriv r :=
    Submodule.eq_of_le_of_finrank_le
      (fun z hz => by
        change ‖z‖ < r.1
        exact lt_of_lt_of_le hz (min_le_left _ _))
      (le_of_not_gt (Function.not_lt_argmin d s))
  have hvball : v ∈ normBall htriv s := heq.symm ▸ hvr
  exact (not_lt_of_ge (min_le_right r.1 ‖v‖)) hvball

private theorem bounded_dual_on_finite_span {F V : Type*} [NormedField F]
    [NormedAddCommGroup V] [NormedSpace F V] [IsUltrametricDist V]
    [FiniteDimensional F V] (htriv : ∀ c : F, ‖c‖ ≤ 1) (φ : V →ₗ[F] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ v, ‖φ v‖ ≤ C * ‖v‖ := by
  obtain ⟨ε, hε, hbound⟩ := norm_lower_bound (V := V) htriv
  refine ⟨ε⁻¹, inv_pos.mpr hε, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · calc ‖φ v‖ ≤ 1 := htriv _
         _ = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
         _ ≤ ε⁻¹ * ‖v‖ := mul_le_mul_of_nonneg_left (hbound v hv) (inv_nonneg.mpr hε.le)

section Positivity

variable {F : Type*} [NormedField F] [CompleteSpace F]
  {E : Type*} [NormedRing E] [NormedAlgebra F E] [IsUltrametricDist E]
  {E' : Type*} [NormedRing E'] [NormedAlgebra F E'] [IsUltrametricDist E']

omit [CompleteSpace F] [IsUltrametricDist E'] in
private theorem reduce_representation {t : E ⊗[F] E'} (r : Representation F E E' t) :
    ∃ (J : Type) (_ : Fintype J) (a : J → E) (b : J → E'), LinearIndependent F b ∧
      ∑ j, a j ⊗ₜ[F] b j = t ∧ ∀ j, ‖a j‖ * ‖b j‖ ≤ r.value := by
  obtain ⟨J, hJ, a, b, hb, hsum, hM⟩ := exists_linearIndependent_right (F := F) _ r.ι r.left
    r.right rfl r.value fun i => by exact_mod_cast r.le_value i
  exact ⟨J, hJ, a, b, hb, hsum.trans r.sum_eq, hM⟩

omit [CompleteSpace F] [IsUltrametricDist E'] in
private theorem exists_dual_lid_rTensor_ne_zero_all {t : E ⊗[F] E'} (ht : t ≠ 0) :
    ∃ φ : Module.Dual F E, TensorProduct.lid F E' (φ.rTensor E' t) ≠ 0 := by
  classical
  obtain ⟨J, _, a, b, hb, hsum, -⟩ :=
    reduce_representation (Representation.nonempty t).some
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ht (by simp [← hsum, h])
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hj₀
  refine ⟨φ, fun h0 => hφ ?_⟩
  rw [← hsum] at h0
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h0
  exact Fintype.linearIndependent_iff.mp hb _ h0 j₀

omit [CompleteSpace F] in
/-- The ultrametric projective tensor seminorm of a nonzero tensor is positive. -/
theorem seminormFun_pos_trivial (htriv : ∀ c : F, ‖c‖ ≤ 1)
    {t : E ⊗[F] E'} (ht : t ≠ 0) : 0 < seminormFun t := by
  classical
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero_all ht
  set w := TensorProduct.lid F E' (φ.rTensor E' t)
  set r₀ := (Representation.nonempty t).some
  set V₀ := Submodule.span F (Set.range r₀.left)
  have : FiniteDimensional F V₀ := FiniteDimensional.span_of_finite F (Set.finite_range _)
  obtain ⟨C, hC, hψ⟩ := bounded_dual_on_finite_span (F := F) htriv (φ ∘ₗ V₀.subtype)
  have hφle (v : E) (hv : v ∈ V₀) : ‖φ v‖ ≤ C * ‖v‖ := hψ ⟨v, hv⟩
  -- Every representation has value at least `‖w‖ / C`.
  have hbound (r : Representation F E E' t) : ‖w‖ ≤ C * r.value := by
    obtain ⟨J, _, a, b, hb, hsum, hM⟩ := reduce_representation r
    have hmem (j : J) : a j ∈ V₀ :=
      mem_span_of_linearIndependent r₀.left r₀.right a b hb (hsum.trans r₀.sum_eq.symm) j
    have hw : w = ∑ j, φ (a j) • b j := by
      simp only [w, ← hsum, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rw [hw]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg hC.le r.value.2) fun j _ => ?_
    calc ‖φ (a j) • b j‖ ≤ ‖φ (a j)‖ * ‖b j‖ := norm_smul_le _ _
      _ ≤ C * ‖a j‖ * ‖b j‖ :=
          mul_le_mul_of_nonneg_right (hφle _ (hmem j)) (norm_nonneg _)
      _ = C * (‖a j‖ * ‖b j‖) := mul_assoc _ _ _
      _ ≤ C * r.value := mul_le_mul_of_nonneg_left (hM j) hC.le
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hφ
  have hle : (‖w‖ / C).toNNReal ≤ seminormFun t := by
    refine le_seminormFun fun r => ?_
    rw [Real.toNNReal_le_iff_le_coe, div_le_iff₀ hC, mul_comm]
    exact hbound r
  exact lt_of_lt_of_le (Real.toNNReal_pos.mpr (div_pos hw0 hC)) hle

theorem seminormFun_pos_all {t : E ⊗[F] E'} (ht : t ≠ 0) : 0 < seminormFun t := by
  by_cases h : ∃ c : F, 1 < ‖c‖
  · let : NontriviallyNormedField F := { ‹NormedField F› with non_trivial := h }
    exact seminormFun_pos ht
  · exact seminormFun_pos_trivial (fun c => le_of_not_gt (fun hc => h ⟨c, hc⟩)) ht

end Positivity

section Completion

variable (F : Type u) [NormedField F] [CompleteSpace F]
  (E : Type v) [NormedCommRing E] [NormedAlgebra F E] [IsUltrametricDist E]
  (E' : Type w) [NormedCommRing E'] [NormedAlgebra F E'] [IsUltrametricDist E']

/-- The ultrametric projective tensor norm on `E ⊗[F] E'`. -/
def tensorRingNorm : RingNorm (E ⊗[F] E') :=
  { ultrametricTensorSeminorm F E E' with
    eq_zero_of_map_eq_zero' := fun t ht => by
      by_contra h
      have h0 : (seminormFun t : ℝ) = 0 := ht
      exact (seminormFun_pos_all (F := F) h).ne' (NNReal.coe_eq_zero.mp h0) }

/-- The algebraic tensor product `E ⊗[F] E'` with the ultrametric projective tensor norm. -/
def NormedTensor : Type _ := E ⊗[F] E'

instance : NormedCommRing (NormedTensor F E E') :=
  { @RingNorm.toNormedRing (NormedTensor F E E') (inferInstanceAs (Ring (E ⊗[F] E')))
      (tensorRingNorm F E E') with
    mul_comm := mul_comm (G := E ⊗[F] E') }

instance : Algebra F (NormedTensor F E E') := inferInstanceAs (Algebra F (E ⊗[F] E'))

theorem norm_def (t : NormedTensor F E E') :
    ‖t‖ = (seminormFun (E := F) (F := E) (G := E') t : ℝ) :=
  rfl

instance : NormedAlgebra F (NormedTensor F E E') :=
  { (inferInstance : Algebra F (NormedTensor F E E')) with
  norm_smul_le c t := by
    rw [norm_def, norm_def]
    exact_mod_cast Langlands.Analytic.UltrametricTensorSeminorm.seminormFun_smul_le c t }

instance : IsUltrametricDist (NormedTensor F E E') :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun s t => by
    rw [norm_def, norm_def, norm_def]
    exact_mod_cast seminormFun_add_le (E := F) (F := E) (G := E') s t

/-- The canonical `F`-algebra map from `E ⊗[F] E'` into the completed tensor product. -/
def toCompletion : E ⊗[F] E' →ₐ[F] UniformSpace.Completion (NormedTensor F E E') :=
  { (UniformSpace.Completion.coeRingHom :
      NormedTensor F E E' →+* UniformSpace.Completion (NormedTensor F E E')) with
    commutes' := fun _ => rfl }

theorem toCompletion_injective : Function.Injective (toCompletion F E E') :=
  fun _ _ h => UniformSpace.Completion.coe_injective (NormedTensor F E E') h

theorem norm_toCompletion_tmul_le (e : E) (e' : E') :
    ‖toCompletion F E E' (e ⊗ₜ[F] e')‖ ≤ ‖e‖ * ‖e'‖ := by
  have h := UniformSpace.Completion.norm_coe (E := NormedTensor F E E') (e ⊗ₜ[F] e')
  exact (le_of_eq h).trans (ultrametricTensorSeminorm_tmul_le (E := F) e e')

end Completion

end Langlands.Analytic.SeparatedFieldTensor
