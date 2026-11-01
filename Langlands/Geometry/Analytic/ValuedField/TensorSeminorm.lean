import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The ultrametric projective tensor seminorm

For normed rings `F` and `G` that are algebras over a commutative ring `E`, the ultrametric
projective tensor seminorm of `t : F ⊗[E] G` is the infimum, over all finite representations
`t = ∑ i, a i ⊗ₜ b i`, of `max_i ‖a i‖ * ‖b i‖`. It is a nonarchimedean ring seminorm bounded by
`‖a‖ * ‖b‖` on pure tensors. When `E`, `F`, `G` are normed fields with `F` and `G` normed
`E`-algebras whose norms are ultrametric, it takes the value `1` at `1`.
-/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Analytic

namespace UltrametricTensorSeminorm

section Construction

variable (E F G : Type*) [CommRing E] [NormedRing F] [NormedRing G] [Algebra E F] [Algebra E G]

/-- A finite representation `t = ∑ i, left i ⊗ₜ right i` of a tensor `t`. -/
structure Representation (t : F ⊗[E] G) where
  /-- The finite index type of the representation. -/
  ι : Type
  /-- The index type is finite. -/
  [fintype : Fintype ι]
  /-- The left factors. -/
  left : ι → F
  /-- The right factors. -/
  right : ι → G
  /-- The representation sums to `t`. -/
  sum_eq : ∑ i, left i ⊗ₜ[E] right i = t

attribute [instance] Representation.fintype

variable {E F G}

namespace Representation

/-- The value `max_i ‖left i‖ * ‖right i‖` of a representation (`0` when it is empty). -/
def value {t : F ⊗[E] G} (r : Representation E F G t) : ℝ≥0 :=
  Finset.univ.sup fun i => ‖r.left i‖₊ * ‖r.right i‖₊

theorem le_value {t : F ⊗[E] G} (r : Representation E F G t) (i : r.ι) :
    ‖r.left i‖₊ * ‖r.right i‖₊ ≤ r.value :=
  Finset.le_sup (f := fun i => ‖r.left i‖₊ * ‖r.right i‖₊) (Finset.mem_univ i)

theorem value_le_iff {t : F ⊗[E] G} (r : Representation E F G t) {c : ℝ≥0} :
    r.value ≤ c ↔ ∀ i, ‖r.left i‖₊ * ‖r.right i‖₊ ≤ c := by
  simp [value, Finset.sup_le_iff]

/-- The empty representation of `0`. -/
def zero : Representation E F G 0 where
  ι := Empty
  left := fun i => i.elim
  right := fun i => i.elim
  sum_eq := by simp

/-- The one-term representation of a pure tensor. -/
def tmul (a : F) (b : G) : Representation E F G (a ⊗ₜ[E] b) where
  ι := Unit
  left := fun _ => a
  right := fun _ => b
  sum_eq := by simp

/-- The concatenation of representations of `t` and `s`, representing `t + s`. -/
def add {t s : F ⊗[E] G} (r : Representation E F G t) (r' : Representation E F G s) :
    Representation E F G (t + s) where
  ι := r.ι ⊕ r'.ι
  left := Sum.elim r.left r'.left
  right := Sum.elim r.right r'.right
  sum_eq := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, r.sum_eq, r'.sum_eq]

/-- Negating the left factors represents `-t`. -/
def neg {t : F ⊗[E] G} (r : Representation E F G t) : Representation E F G (-t) where
  ι := r.ι
  left := fun i => -r.left i
  right := r.right
  sum_eq := by
    simp only [TensorProduct.neg_tmul, Finset.sum_neg_distrib, r.sum_eq]

/-- The termwise product of representations of `t` and `s`, representing `t * s`. -/
def mul {t s : F ⊗[E] G} (r : Representation E F G t) (r' : Representation E F G s) :
    Representation E F G (t * s) where
  ι := r.ι × r'.ι
  left := fun p => r.left p.1 * r'.left p.2
  right := fun p => r.right p.1 * r'.right p.2
  sum_eq := by
    conv_rhs => rw [← r.sum_eq, ← r'.sum_eq]
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [Algebra.TensorProduct.tmul_mul_tmul]

theorem value_zero : (zero : Representation E F G 0).value = 0 := by
  simp [value, zero]

theorem value_tmul (a : F) (b : G) : (tmul (E := E) a b).value = ‖a‖₊ * ‖b‖₊ := by
  simp only [value, tmul]
  exact Finset.sup_const Finset.univ_nonempty _

theorem value_add_le {t s : F ⊗[E] G} (r : Representation E F G t)
    (r' : Representation E F G s) : (r.add r').value ≤ max r.value r'.value := by
  rw [value_le_iff]
  rintro (i | i)
  · exact le_max_of_le_left (r.le_value i)
  · exact le_max_of_le_right (r'.le_value i)

theorem value_neg {t : F ⊗[E] G} (r : Representation E F G t) : r.neg.value = r.value := by
  simp only [value, neg, nnnorm_neg]
  rfl

theorem value_mul_le {t s : F ⊗[E] G} (r : Representation E F G t)
    (r' : Representation E F G s) : (r.mul r').value ≤ r.value * r'.value := by
  rw [value_le_iff]
  rintro ⟨i, j⟩
  calc ‖r.left i * r'.left j‖₊ * ‖r.right i * r'.right j‖₊
      ≤ (‖r.left i‖₊ * ‖r'.left j‖₊) * (‖r.right i‖₊ * ‖r'.right j‖₊) :=
        mul_le_mul' (nnnorm_mul_le _ _) (nnnorm_mul_le _ _)
    _ = (‖r.left i‖₊ * ‖r.right i‖₊) * (‖r'.left j‖₊ * ‖r'.right j‖₊) := by ring
    _ ≤ r.value * r'.value := mul_le_mul' (r.le_value i) (r'.le_value j)

instance nonempty (t : F ⊗[E] G) : Nonempty (Representation E F G t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact ⟨tmul a b⟩
  | add x y hx hy => exact ⟨hx.some.add hy.some⟩

end Representation

/-- The infimum of the values of all finite representations of `t`. -/
def seminormFun (t : F ⊗[E] G) : ℝ≥0 :=
  ⨅ r : Representation E F G t, r.value

theorem seminormFun_le {t : F ⊗[E] G} (r : Representation E F G t) :
    seminormFun t ≤ r.value :=
  ciInf_le (OrderBot.bddBelow _) r

theorem le_seminormFun {t : F ⊗[E] G} {c : ℝ≥0} (h : ∀ r : Representation E F G t, c ≤ r.value) :
    c ≤ seminormFun t :=
  le_ciInf h

theorem seminormFun_zero : seminormFun (0 : F ⊗[E] G) = 0 :=
  le_antisymm ((seminormFun_le Representation.zero).trans_eq Representation.value_zero)
    zero_le

theorem seminormFun_tmul_le (a : F) (b : G) : seminormFun (a ⊗ₜ[E] b) ≤ ‖a‖₊ * ‖b‖₊ :=
  (seminormFun_le (Representation.tmul a b)).trans_eq (Representation.value_tmul a b)

theorem seminormFun_add_le (t s : F ⊗[E] G) :
    seminormFun (t + s) ≤ max (seminormFun t) (seminormFun s) := by
  by_contra h
  rw [not_le] at h
  obtain ⟨r, hr⟩ := exists_lt_of_ciInf_lt (f := fun r : Representation E F G t => r.value)
    ((le_max_left _ _).trans_lt h)
  obtain ⟨r', hr'⟩ := exists_lt_of_ciInf_lt (f := fun r : Representation E F G s => r.value)
    ((le_max_right _ _).trans_lt h)
  exact ((seminormFun_le (r.add r')).trans (r.value_add_le r')).not_gt (max_lt hr hr')

theorem seminormFun_neg_le (t : F ⊗[E] G) : seminormFun (-t) ≤ seminormFun t :=
  le_seminormFun fun r => (seminormFun_le r.neg).trans_eq r.value_neg

theorem seminormFun_neg (t : F ⊗[E] G) : seminormFun (-t) = seminormFun t :=
  le_antisymm (seminormFun_neg_le t) (by simpa using seminormFun_neg_le (-t))

theorem seminormFun_mul_le (t s : F ⊗[E] G) :
    seminormFun (t * s) ≤ seminormFun t * seminormFun s :=
  NNReal.le_iInf_mul fun r => NNReal.le_mul_iInf fun r' =>
    (seminormFun_le (r.mul r')).trans (r.value_mul_le r')

end Construction

end UltrametricTensorSeminorm

open UltrametricTensorSeminorm

section Construction

variable (E F G : Type*) [CommRing E] [NormedRing F] [NormedRing G] [Algebra E F] [Algebra E G]

/-- The ultrametric projective tensor seminorm on `F ⊗[E] G`: the infimum over finite
representations `t = ∑ i, a i ⊗ₜ b i` of `max_i ‖a i‖ * ‖b i‖`. -/
def ultrametricTensorSeminorm : RingSeminorm (F ⊗[E] G) where
  toFun t := seminormFun t
  map_zero' := by simp [seminormFun_zero]
  add_le' t s := by
    have h := seminormFun_add_le t s
    have h' : max (seminormFun t) (seminormFun s) ≤ seminormFun t + seminormFun s :=
      max_le le_self_add le_add_self
    exact_mod_cast h.trans h'
  neg' t := by simp [seminormFun_neg]
  mul_le' t s := by exact_mod_cast seminormFun_mul_le t s

variable {E F G}

theorem ultrametricTensorSeminorm_apply (t : F ⊗[E] G) :
    ultrametricTensorSeminorm E F G t = seminormFun t :=
  rfl

theorem isNonarchimedean_ultrametricTensorSeminorm :
    IsNonarchimedean (ultrametricTensorSeminorm E F G) := by
  intro t s
  simp only [ultrametricTensorSeminorm_apply]
  exact_mod_cast seminormFun_add_le t s

theorem ultrametricTensorSeminorm_tmul_le (a : F) (b : G) :
    ultrametricTensorSeminorm E F G (a ⊗ₜ[E] b) ≤ ‖a‖ * ‖b‖ := by
  rw [ultrametricTensorSeminorm_apply]
  exact_mod_cast seminormFun_tmul_le a b

end Construction

namespace UltrametricTensorSeminorm

section LowerBound

variable {E F G : Type*} [NormedField E] [NormedField F] [IsUltrametricDist F]
  [NormedField G] [IsUltrametricDist G] [NormedAlgebra E F] [NormedAlgebra E G]

omit [IsUltrametricDist F] in
/-- If `1 = ∑ i, a i ⊗ₜ b i` with linearly independent right factors, then
`1 ≤ max_i ‖a i‖ * ‖b i‖`. -/
theorem one_le_of_linearIndependent {ι : Type*} [Fintype ι] (a : ι → F) (b : ι → G)
    (hb : LinearIndependent E b) (hab : ∑ i, a i ⊗ₜ[E] b i = 1) {M : ℝ}
    (hM : ∀ i, ‖a i‖ * ‖b i‖ ≤ M) : 1 ≤ M := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination E b).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hb.fintypeLinearCombination_injective)
  have hgb (i : ι) : g (b i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h
  obtain ⟨ψ, hψ⟩ := (Algebra.linearMap E F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap E F).injective)
  have hψ' (c : E) : ψ (algebraMap E F c) = c := LinearMap.congr_fun hψ c
  have hψ1 : ψ 1 = 1 := by simpa using hψ' 1
  -- Applying `id ⊗ (j-th coordinate of g)` shows that each left factor is a scalar.
  have ha (j : ι) : a j = algebraMap E F (g 1 j) := by
    have h := congrArg
      ((TensorProduct.rid E F).toLinearMap ∘ₗ ((LinearMap.proj j ∘ₗ g).lTensor F)) hab
    simp only [map_sum, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.rid_tmul, LinearMap.proj_apply, hgb, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Algebra.TensorProduct.one_def] at h
    rw [h, Algebra.algebraMap_eq_smul_one]
  -- Applying `ψ ⊗ id` then expresses `1 : G` through the right factors.
  have hsum : ∑ i, g 1 i • b i = 1 := by
    have h := congrArg ((TensorProduct.lid E G).toLinearMap ∘ₗ ψ.rTensor G) hab
    simp only [map_sum, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, ha, hψ', Algebra.TensorProduct.one_def, hψ1, one_smul] at h
    exact h
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [Finset.univ_eq_empty] at hsum
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hM i₀)
  have h1 : ‖(1 : G)‖ ≤ M := by
    rw [← hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun i _ => ?_
    rw [norm_smul, ← norm_algebraMap' F (g 1 i), ← ha]
    exact hM i
  simpa using h1

private theorem one_le_aux (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] (a : ι → F) (b : ι → G), Fintype.card ι = n →
      ∑ i, a i ⊗ₜ[E] b i = 1 → ∀ M : ℝ, (∀ i, ‖a i‖ * ‖b i‖ ≤ M) → 1 ≤ M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ a b hn hab M hM
  classical
  by_cases hli : LinearIndependent E b
  · exact one_le_of_linearIndependent a b hli hab hM
  -- Some right factor `b k` is a combination of the others with controlled coefficients.
  obtain ⟨k, d, hbk, hd⟩ : ∃ k, ∃ d : ι → E,
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
  -- Eliminate `b k`; the new representation has one term fewer and no larger value.
  refine ih (Fintype.card {i // i ≠ k}) ?_ {i // i ≠ k} (fun i => a i + d i • a k)
    (fun i => b i) rfl ?_ M ?_
  · rw [← hn]
    exact Fintype.card_subtype_lt (p := fun i => i ≠ k) (x := k) (by simp)
  · calc ∑ i : {i // i ≠ k}, (a i + d i • a k) ⊗ₜ[E] b i
        = ∑ i : {i // i ≠ k}, a i ⊗ₜ[E] b i + a k ⊗ₜ[E] ∑ i : {i // i ≠ k}, d i • b i := by
          simp only [TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul,
            TensorProduct.tmul_sum]
      _ = ∑ i, a i ⊗ₜ[E] b i := by
          rw [← hbk, Fintype.sum_eq_add_sum_subtype_ne _ k, add_comm]
      _ = 1 := hab
  · intro i
    rcases le_max_iff.mp (IsUltrametricDist.norm_add_le_max (a i) (d i • a k)) with h | h
    · exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans (hM i)
    · calc ‖a i + d i • a k‖ * ‖b i‖ ≤ ‖d i • a k‖ * ‖b i‖ :=
            mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = ‖a k‖ * (‖d i‖ * ‖b i‖) := by rw [norm_smul]; ring
        _ ≤ ‖a k‖ * ‖b k‖ := mul_le_mul_of_nonneg_left (hd i) (norm_nonneg _)
        _ ≤ M := hM k

/-- Every finite representation `1 = ∑ i, a i ⊗ₜ b i` has `1 ≤ max_i ‖a i‖ * ‖b i‖`. -/
theorem one_le_of_sum_tmul_eq_one {ι : Type} [Fintype ι] (a : ι → F) (b : ι → G)
    (hab : ∑ i, a i ⊗ₜ[E] b i = 1) {M : ℝ} (hM : ∀ i, ‖a i‖ * ‖b i‖ ≤ M) : 1 ≤ M :=
  one_le_aux _ ι a b rfl hab M hM

theorem one_le_value (r : Representation E F G 1) : 1 ≤ r.value := by
  have h := one_le_of_sum_tmul_eq_one r.left r.right r.sum_eq (M := r.value)
    fun i => by exact_mod_cast r.le_value i
  exact_mod_cast h

end LowerBound

end UltrametricTensorSeminorm

section Normalized

variable {E F G : Type*} [NormedField E] [NormedField F] [IsUltrametricDist F]
  [NormedField G] [IsUltrametricDist G] [NormedAlgebra E F] [NormedAlgebra E G]

theorem ultrametricTensorSeminorm_one : ultrametricTensorSeminorm E F G 1 = 1 := by
  rw [ultrametricTensorSeminorm_apply, NNReal.coe_eq_one]
  refine le_antisymm ?_ (le_seminormFun one_le_value)
  rw [Algebra.TensorProduct.one_def]
  simpa using seminormFun_tmul_le (E := E) (1 : F) (1 : G)

/-- Over ultrametric normed fields, the ultrametric projective tensor seminorm is a normalized
nonarchimedean ring seminorm with `p (a ⊗ₜ 1) ≤ ‖a‖` and `p (1 ⊗ₜ b) ≤ ‖b‖`. -/
theorem exists_ultrametricTensorSeminorm :
    ∃ p : RingSeminorm (F ⊗[E] G), p 1 = 1 ∧ IsNonarchimedean p ∧
      (∀ a : F, p (a ⊗ₜ[E] (1 : G)) ≤ ‖a‖) ∧ (∀ b : G, p ((1 : F) ⊗ₜ[E] b) ≤ ‖b‖) :=
  ⟨ultrametricTensorSeminorm E F G, ultrametricTensorSeminorm_one,
    isNonarchimedean_ultrametricTensorSeminorm,
    fun a => by simpa using ultrametricTensorSeminorm_tmul_le (E := E) a (1 : G),
    fun b => by simpa using ultrametricTensorSeminorm_tmul_le (E := E) (1 : F) b⟩

end Normalized

end Langlands.Analytic
