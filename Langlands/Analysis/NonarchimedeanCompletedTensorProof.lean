import Langlands.Analysis.UltrametricCompletion
import Langlands.Analysis.NonarchimedeanCompletedTensorStatement
import Langlands.Geometry.Analytic.ValuedField.TensorSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The ultrametric projective tensor seminorm is a norm

Over a complete nontrivially normed ultrametric field `F`, the ultrametric projective tensor
seminorm on `E ⊗[F] E'` (for ultrametric normed `F`-algebras `E`, `E'`) vanishes only at `0`.
The completion of `E ⊗[F] E'` for this norm proves
`Langlands.Analysis.NonarchimedeanCompletedTensorStatement`.

The positivity proof avoids orthogonal bases: every representation of a tensor can be shortened
to one with linearly independent right factors without increasing its value; the left factors of
such a representation lie in the span of the left factors of one fixed representation; and a
linear functional is bounded on that finite-dimensional span.
-/

noncomputable section

universe u

open scoped TensorProduct NNReal

namespace Langlands.Analysis

namespace NonarchimedeanCompletedTensorProof

open Langlands.Analytic Langlands.Analytic.UltrametricTensorSeminorm

section Reduction

variable {F : Type*} [NormedField F]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace F X] [IsUltrametricDist X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace F Y]

/-- A finite sum of pure tensors can be rewritten with linearly independent right factors,
keeping every product `‖a j‖ * ‖b j‖` below a given bound. -/
theorem exists_linearIndependent_right (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] (a : ι → X) (b : ι → Y), Fintype.card ι = n →
      ∀ M : ℝ, (∀ i, ‖a i‖ * ‖b i‖ ≤ M) →
      ∃ (J : Type) (_ : Fintype J) (a' : J → X) (b' : J → Y), LinearIndependent F b' ∧
        ∑ j, a' j ⊗ₜ[F] b' j = ∑ i, a i ⊗ₜ[F] b i ∧ ∀ j, ‖a' j‖ * ‖b' j‖ ≤ M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ a b hn M hM
  classical
  by_cases hli : LinearIndependent F b
  · exact ⟨ι, inferInstance, a, b, hli, rfl, hM⟩
  -- Some right factor `b k` is a combination of the others with controlled coefficients.
  obtain ⟨k, d, hbk, hd⟩ : ∃ k, ∃ d : ι → F,
      b k = ∑ i : {i // i ≠ k}, d i • b i ∧ ∀ i, ‖d i‖ * ‖b i‖ ≤ ‖b k‖ := by
    obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hli
    by_cases hbj : b j = 0
    · exact ⟨j, 0, by simp [hbj], fun i => by simp⟩
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
      (fun i => ‖c i‖ * ‖b i‖) ⟨j, Finset.mem_univ j⟩
    have hck : c k ≠ 0 := by
      intro h0
      have h := hk j (Finset.mem_univ j)
      rw [h0, norm_zero, zero_mul] at h
      have : 0 < ‖c j‖ * ‖b j‖ := mul_pos (norm_pos_iff.mpr hj) (norm_pos_iff.mpr hbj)
      linarith
    refine ⟨k, fun i => -(c k)⁻¹ * c i, ?_, fun i => ?_⟩
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ k] at hc
      have h1 : c k • b k = -∑ i : {i // i ≠ k}, c i • b i := eq_neg_of_add_eq_zero_left hc
      calc b k = (c k)⁻¹ • (c k • b k) := by rw [smul_smul, inv_mul_cancel₀ hck, one_smul]
        _ = ∑ i : {i // i ≠ k}, (-(c k)⁻¹ * c i) • b i := by
          rw [h1, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          simp only [smul_smul, neg_mul, neg_smul]
    · rw [norm_mul, norm_neg, norm_inv, mul_assoc]
      calc ‖c k‖⁻¹ * (‖c i‖ * ‖b i‖) ≤ ‖c k‖⁻¹ * (‖c k‖ * ‖b k‖) :=
            mul_le_mul_of_nonneg_left (hk i (Finset.mem_univ i)) (by positivity)
        _ = ‖b k‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hck), one_mul]
  -- Eliminate `b k`; the new representation has one term fewer and no larger products.
  have hcard : Fintype.card {i // i ≠ k} < n := by
    rw [← hn]
    exact Fintype.card_subtype_lt (p := fun i => i ≠ k) (x := k) (by simp)
  have hbound : ∀ i : {i // i ≠ k}, ‖a i + d i • a k‖ * ‖b i‖ ≤ M := by
    intro i
    rcases le_max_iff.mp (IsUltrametricDist.norm_add_le_max (a i) (d i • a k)) with h | h
    · exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans (hM i)
    · calc ‖a i + d i • a k‖ * ‖b i‖ ≤ ‖d i • a k‖ * ‖b i‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ ≤ (‖d i‖ * ‖a k‖) * ‖b i‖ :=
            mul_le_mul_of_nonneg_right (norm_smul_le _ _) (norm_nonneg _)
        _ = ‖a k‖ * (‖d i‖ * ‖b i‖) := by ring
        _ ≤ ‖a k‖ * ‖b k‖ := mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _)
        _ ≤ M := hM k
  obtain ⟨J, hJ, a', b', hb', hsum, hM'⟩ := ih _ hcard {i // i ≠ k}
    (fun i => a i + d i • a k) (fun i => b i) rfl M hbound
  refine ⟨J, hJ, a', b', hb', ?_, hM'⟩
  rw [hsum]
  calc ∑ i : {i // i ≠ k}, (a i + d i • a k) ⊗ₜ[F] b i
      = ∑ i : {i // i ≠ k}, a i ⊗ₜ[F] b i + a k ⊗ₜ[F] ∑ i : {i // i ≠ k}, d i • b i := by
        simp only [TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul,
          TensorProduct.tmul_sum]
    _ = ∑ i, a i ⊗ₜ[F] b i := by
        rw [← hbk, Fintype.sum_eq_add_sum_subtype_ne _ k, add_comm]

omit [IsUltrametricDist X] in
/-- If `t = ∑ p, e p ⊗ₜ f p` and also `t = ∑ j, a j ⊗ₜ b j` with linearly independent right
factors `b`, then every `a j` lies in the span of the `e p`. -/
theorem mem_span_of_linearIndependent {P J : Type*} [Fintype P] [Fintype J]
    (e : P → X) (f : P → Y) (a : J → X) (b : J → Y) (hb : LinearIndependent F b)
    (h : ∑ j, a j ⊗ₜ[F] b j = ∑ p, e p ⊗ₜ[F] f p) (j : J) :
    a j ∈ Submodule.span F (Set.range e) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination F b).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hb.fintypeLinearCombination_injective)
  have hgb (i : J) : g (b i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h
  have h' := congrArg
    ((TensorProduct.rid F X).toLinearMap ∘ₗ ((LinearMap.proj j ∘ₗ g).lTensor X)) h
  simp only [map_sum, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, LinearMap.proj_apply, hgb, Pi.single_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h'
  rw [h']
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p))

end Reduction

section Positivity

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]
  {E : Type*} [NormedRing E] [NormedAlgebra F E] [IsUltrametricDist E]
  {E' : Type*} [NormedRing E'] [NormedAlgebra F E'] [IsUltrametricDist E']

omit [CompleteSpace F] [IsUltrametricDist E'] in
/-- Every representation of `t` can be shortened to one with linearly independent right factors
and no larger value. -/
theorem exists_linearIndependent_of_representation {t : E ⊗[F] E'}
    (r : Representation F E E' t) :
    ∃ (J : Type) (_ : Fintype J) (a : J → E) (b : J → E'), LinearIndependent F b ∧
      ∑ j, a j ⊗ₜ[F] b j = t ∧ ∀ j, ‖a j‖ * ‖b j‖ ≤ r.value := by
  obtain ⟨J, hJ, a, b, hb, hsum, hM⟩ := exists_linearIndependent_right (F := F) _ r.ι r.left
    r.right rfl r.value fun i => by exact_mod_cast r.le_value i
  exact ⟨J, hJ, a, b, hb, hsum.trans r.sum_eq, hM⟩

omit [CompleteSpace F] [IsUltrametricDist E'] in
/-- A nonzero tensor is detected by some functional applied to its left factors. -/
theorem exists_dual_lid_rTensor_ne_zero {t : E ⊗[F] E'} (ht : t ≠ 0) :
    ∃ φ : Module.Dual F E, TensorProduct.lid F E' (φ.rTensor E' t) ≠ 0 := by
  classical
  obtain ⟨J, _, a, b, hb, hsum, -⟩ :=
    exists_linearIndependent_of_representation (Representation.nonempty t).some
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ht (by simp [← hsum, h])
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hj₀
  refine ⟨φ, fun h0 => hφ ?_⟩
  rw [← hsum] at h0
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h0
  exact Fintype.linearIndependent_iff.mp hb _ h0 j₀

/-- The ultrametric projective tensor seminorm of a nonzero tensor is positive. -/
theorem seminormFun_pos {t : E ⊗[F] E'} (ht : t ≠ 0) : 0 < seminormFun t := by
  classical
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero ht
  set w := TensorProduct.lid F E' (φ.rTensor E' t)
  set r₀ := (Representation.nonempty t).some
  set V₀ := Submodule.span F (Set.range r₀.left)
  have : FiniteDimensional F V₀ := FiniteDimensional.span_of_finite F (Set.finite_range _)
  set ψ : V₀ →L[F] F := LinearMap.toContinuousLinearMap (φ ∘ₗ V₀.subtype)
  set C : ℝ := max ‖ψ‖ 1
  have hC : 0 < C := lt_max_of_lt_right one_pos
  have hφle (v : E) (hv : v ∈ V₀) : ‖φ v‖ ≤ C * ‖v‖ :=
    calc ‖φ v‖ = ‖ψ ⟨v, hv⟩‖ := rfl
      _ ≤ ‖ψ‖ * ‖(⟨v, hv⟩ : V₀)‖ := ψ.le_opNorm _
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  -- Every representation has value at least `‖w‖ / C`.
  have hbound (r : Representation F E E' t) : ‖w‖ ≤ C * r.value := by
    obtain ⟨J, _, a, b, hb, hsum, hM⟩ := exists_linearIndependent_of_representation r
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

omit [CompleteSpace F] [IsUltrametricDist E] [IsUltrametricDist E'] in
/-- Scalars are bounded for the ultrametric projective tensor seminorm. -/
theorem seminormFun_smul_le (c : F) (t : E ⊗[F] E') :
    seminormFun (c • t) ≤ ‖c‖₊ * seminormFun t := by
  refine NNReal.le_mul_iInf fun r => ?_
  let r' : Representation F E E' (c • t) :=
    { ι := r.ι
      left := fun i => c • r.left i
      right := r.right
      sum_eq := by
        simp only [← TensorProduct.smul_tmul', ← Finset.smul_sum, r.sum_eq] }
  refine (seminormFun_le r').trans ?_
  rw [Representation.value_le_iff]
  intro i
  calc ‖c • r.left i‖₊ * ‖r.right i‖₊ ≤ (‖c‖₊ * ‖r.left i‖₊) * ‖r.right i‖₊ :=
        mul_le_mul_left (nnnorm_smul_le _ _) _
    _ = ‖c‖₊ * (‖r.left i‖₊ * ‖r.right i‖₊) := mul_assoc _ _ _
    _ ≤ ‖c‖₊ * r.value := mul_le_mul_right (r.le_value i) _

end Positivity

section Completion

variable (F : Type*) [NontriviallyNormedField F] [CompleteSpace F]
  (E : Type*) [NormedCommRing E] [NormedAlgebra F E] [IsUltrametricDist E]
  (E' : Type*) [NormedCommRing E'] [NormedAlgebra F E'] [IsUltrametricDist E']

/-- The ultrametric projective tensor norm on `E ⊗[F] E'`. -/
def tensorRingNorm : RingNorm (E ⊗[F] E') :=
  { ultrametricTensorSeminorm F E E' with
    eq_zero_of_map_eq_zero' := fun t ht => by
      by_contra h
      have h0 : (seminormFun t : ℝ) = 0 := ht
      exact (seminormFun_pos (F := F) h).ne' (NNReal.coe_eq_zero.mp h0) }

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
    exact_mod_cast seminormFun_smul_le (E := E) (E' := E') c t }

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

end NonarchimedeanCompletedTensorProof

open NonarchimedeanCompletedTensorProof in
/-- Gruson–van der Put, Lemma 5.2(2): the completed ultrametric projective tensor product
contains the algebraic tensor product. -/
theorem nonarchimedeanCompletedTensor : NonarchimedeanCompletedTensorStatement.{u} := by
  intro F _ _ _ E _ _ _ E' _ _ _
  exact ⟨UniformSpace.Completion (NormedTensor F E E'), inferInstance, inferInstance,
    inferInstance, inferInstance, toCompletion F E E', toCompletion_injective F E E',
    norm_toCompletion_tmul_le F E E'⟩

end Langlands.Analysis
