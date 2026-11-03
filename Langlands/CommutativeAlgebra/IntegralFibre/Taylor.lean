import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Truncated Taylor expansion along a section -/

open TensorProduct MvPolynomial

namespace Langlands.CommutativeAlgebra.IntegralFibre

section Taylor

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (σ : S →ₐ[A] A) {d : ℕ} (t : Fin d → S)

/-- Exponent vectors of total degree `< k`. -/
abbrev Mon (d k : ℕ) := {α : Fin d →₀ ℕ // α.degree < k}

/-- The monomial `t ^ α`. -/
noncomputable def tpow (α : Fin d →₀ ℕ) : S := aeval t (monomial α (1 : A))

lemma aeval_mem_ker_pow (ht : ∀ i, σ (t i) = 0) {m : ℕ} {p : MvPolynomial (Fin d) A}
    (hp : p ∈ idealOfVars (Fin d) A ^ m) : aeval t p ∈ RingHom.ker σ ^ m := by
  have h1 : Ideal.map (aeval t) (idealOfVars (Fin d) A) ≤ RingHom.ker σ := by
    rw [Ideal.map_le_iff_le_comap, idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [ht i]
  have h2 : aeval t p ∈ Ideal.map (aeval t) (idealOfVars (Fin d) A ^ m) :=
    Ideal.mem_map_of_mem _ hp
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 m h2

lemma tpow_mem_ker_pow (ht : ∀ i, σ (t i) = 0) (α : Fin d →₀ ℕ) :
    tpow (A := A) t α ∈ RingHom.ker σ ^ α.degree :=
  aeval_mem_ker_pow σ t ht ((mem_pow_idealOfVars_iff' _ _).mpr fun x hx ↦ by
    rw [coeff_monomial, ite_eq_right_iff.mpr (fun e ↦ absurd (e ▸ hx) (lt_irrefl _))])

/-- The truncated Taylor comparison map `A[T]/(T)^k → S/J^k`, on the monomial basis. -/
noncomputable def theta (k : ℕ) : (Mon d k →₀ A) →ₗ[A] S ⧸ RingHom.ker σ ^ k :=
  Finsupp.linearCombination A fun α ↦ Ideal.Quotient.mk _ (tpow (A := A) t α.1)

lemma theta_single (k : ℕ) (α : Mon d k) (a : A) :
    theta σ t k (Finsupp.single α a) = a • Ideal.Quotient.mk _ (tpow (A := A) t α.1) := by
  simp [theta]

/-- Restriction of coefficient vectors to lower degree. -/
noncomputable def restr {k k' : ℕ} (h : k ≤ k') : (Mon d k' →₀ A) →ₗ[A] (Mon d k →₀ A) :=
  Finsupp.lcomapDomain (fun α : Mon d k ↦ (⟨α.1, α.2.trans_le h⟩ : Mon d k'))
    (by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab)

lemma restr_apply {k k' : ℕ} (h : k ≤ k') (v : Mon d k' →₀ A) (α : Mon d k) :
    restr h v α = v ⟨α.1, α.2.trans_le h⟩ := rfl

lemma theta_restr (ht : ∀ i, σ (t i) = 0) {k k' : ℕ} (h : k ≤ k') (v : Mon d k' →₀ A) :
    theta σ t k (restr h v) = Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)
      (theta σ t k' v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single β a =>
    by_cases hβ : β.1.degree < k
    · have : restr h (Finsupp.single β a) = Finsupp.single ⟨β.1, hβ⟩ a := by
        ext γ
        simp only [restr_apply, Finsupp.single_apply]
        congr 1
        exact propext ⟨fun e ↦ Subtype.ext (by simpa using congrArg Subtype.val e),
          fun e ↦ Subtype.ext (by simpa using congrArg Subtype.val e)⟩
      rw [this, theta_single, theta_single, map_smul]
      rfl
    · have : restr h (Finsupp.single β a) = 0 := by
        ext γ
        simp only [restr_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
        refine ite_eq_right_iff.mpr fun e ↦ absurd ?_ hβ
        rw [e]
        exact γ.2
      rw [this, map_zero, theta_single, map_smul]
      symm
      convert smul_zero a
      change Ideal.Quotient.mk _ (tpow (A := A) t β.1) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right (not_lt.mp hβ) (tpow_mem_ker_pow σ t ht β.1)

lemma aeval_monomial_eq_smul_tpow (β : Fin d →₀ ℕ) (c : A) :
    aeval t (monomial β c) = c • tpow (A := A) t β := by
  simp [tpow, aeval_monomial, Algebra.smul_def]

lemma aeval_eq_sum_tpow (p : MvPolynomial (Fin d) A) :
    aeval t p = ∑ β ∈ p.support, p.coeff β • tpow (A := A) t β := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun β _ ↦ aeval_monomial_eq_smul_tpow t β _

/-- One step of the Taylor approximation. -/
lemma exists_approx_step (ht : ∀ i, σ (t i) = 0)
    (hJ : RingHom.ker σ ≤ Ideal.span (Set.range t) ⊔ RingHom.ker σ ^ 2) (m : ℕ) :
    ∀ x ∈ RingHom.ker σ ^ m, ∃ p ∈ idealOfVars (Fin d) A ^ m,
      x - aeval t p ∈ RingHom.ker σ ^ (m + 1) := by
  have base1 : ∀ x ∈ RingHom.ker σ, ∃ p ∈ idealOfVars (Fin d) A,
      x - aeval t p ∈ RingHom.ker σ ^ 2 := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hJ hx)
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hy
    refine ⟨∑ i, C (σ (c i)) * X i, ?_, ?_⟩
    · exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · have : (∑ i, c i * t i + z) - aeval t (∑ i, C (σ (c i)) * X i) =
          ∑ i, (c i - algebraMap A S (σ (c i))) * t i + z := by
        simp only [map_sum, map_mul, aeval_C, aeval_X, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ ↦ ?_) hz
      rw [pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · simp [RingHom.mem_ker]
      · simp [RingHom.mem_ker, ht i]
  induction m with
  | zero =>
    intro x _
    refine ⟨C (σ x), by simp, ?_⟩
    simp [RingHom.mem_ker]
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨pa, hpa, hra⟩ := ih a ha
      obtain ⟨pb, hpb, hrb⟩ := base1 b hb
      refine ⟨pa * pb, by rw [pow_succ]; exact Ideal.mul_mem_mul hpa hpb, ?_⟩
      have hA : aeval t pa ∈ RingHom.ker σ ^ m := aeval_mem_ker_pow σ t ht hpa
      have hB : aeval t pb ∈ RingHom.ker σ ^ 1 := aeval_mem_ker_pow σ t ht (by simpa using hpb)
      have : a * b - aeval t (pa * pb) = aeval t pa * (b - aeval t pb) +
          (a - aeval t pa) * aeval t pb + (a - aeval t pa) * (b - aeval t pb) := by
        rw [map_mul]; ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · have := Ideal.mul_mem_mul hA hrb
        rwa [← pow_add] at this
      · have := Ideal.mul_mem_mul hra hB
        rwa [← pow_add] at this
      · have := Ideal.mul_mem_mul hra hrb
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
    · rintro x y ⟨px, hpx, hx⟩ ⟨py, hpy, hy⟩
      refine ⟨px + py, Ideal.add_mem _ hpx hpy, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hx hy

lemma exists_aeval_sub_mem (ht : ∀ i, σ (t i) = 0)
    (hJ : RingHom.ker σ ≤ Ideal.span (Set.range t) ⊔ RingHom.ker σ ^ 2) (m : ℕ) (s : S) :
    ∃ p : MvPolynomial (Fin d) A, s - aeval t p ∈ RingHom.ker σ ^ m := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, -, hq⟩ := exists_approx_step σ t ht hJ m _ hp
    exact ⟨p + q, by rwa [map_add, ← sub_sub]⟩

lemma theta_surjective (ht : ∀ i, σ (t i) = 0)
    (hJ : RingHom.ker σ ≤ Ideal.span (Set.range t) ⊔ RingHom.ker σ ^ 2) (k : ℕ) :
    Function.Surjective (theta σ t k) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, hp⟩ := exists_aeval_sub_mem σ t ht hJ k s
  have hs : Ideal.Quotient.mk (RingHom.ker σ ^ k) s =
      Ideal.Quotient.mk (RingHom.ker σ ^ k) (aeval t p) := by
    rw [Ideal.Quotient.eq]; exact hp
  have hβ : ∀ β : Fin d →₀ ℕ,
      Ideal.Quotient.mk (RingHom.ker σ ^ k) (tpow (A := A) t β) ∈ LinearMap.range (theta σ t k) := by
    intro β
    by_cases hβ : β.degree < k
    · exact ⟨Finsupp.single ⟨β, hβ⟩ 1, by rw [theta_single, one_smul]⟩
    · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_le_pow_right (not_lt.mp hβ) (tpow_mem_ker_pow σ t ht β))]
      exact Submodule.zero_mem _
  rw [hs, aeval_eq_sum_tpow, map_sum]
  refine Submodule.sum_mem _ fun β _ ↦ ?_
  rw [← Ideal.Quotient.mkₐ_eq_mk A, map_smul, Ideal.Quotient.mkₐ_eq_mk]
  exact Submodule.smul_mem _ _ (hβ β)

omit [Algebra A S] in
lemma monomial_one_mem_pow (α : Fin d →₀ ℕ) :
    monomial α (1 : A) ∈ idealOfVars (Fin d) A ^ α.degree :=
  (mem_pow_idealOfVars_iff' _ _).mpr fun x hx ↦ by
    rw [coeff_monomial, ite_eq_right_iff.mpr (fun e ↦ absurd (e ▸ hx) (lt_irrefl _))]

omit [Algebra A S] in
lemma mul_sub_mul_mem_pow {I : Ideal (MvPolynomial (Fin d) A)} {x y x' y' : MvPolynomial (Fin d) A}
    {m n : ℕ} (h : x - y ∈ I ^ (m + 1)) (hy : y ∈ I ^ m) (h' : x' - y' ∈ I ^ (n + 1))
    (hy' : y' ∈ I ^ n) : x * x' - y * y' ∈ I ^ (m + n + 1) := by
  have hx' : x' ∈ I ^ n := by
    have : x' = (x' - y') + y' := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) h') hy'
  have : x * x' - y * y' = (x - y) * x' + y * (x' - y') := by ring
  rw [this]
  refine Ideal.add_mem _ ?_ ?_
  · have := Ideal.mul_mem_mul h hx'
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this
  · have := Ideal.mul_mem_mul hy h'
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this

omit [Algebra A S] in
lemma aeval_monomial_sub_mem {q : Fin d → MvPolynomial (Fin d) A}
    (hq : ∀ i, q i - X i ∈ idealOfVars (Fin d) A ^ 2) (α : Fin d →₀ ℕ) :
    aeval q (monomial α (1 : A)) - monomial α 1 ∈ idealOfVars (Fin d) A ^ (α.degree + 1) := by
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have := mul_sub_mul_mem_pow hf (monomial_one_mem_pow f) hg (monomial_one_mem_pow g)
    rw [show monomial (f + g) (1 : A) = monomial f 1 * monomial g 1 by rw [monomial_mul_monomial, one_mul],
      map_mul, map_add]
    exact this
  | single a b =>
    rw [Finsupp.degree_single, ← X_pow_eq_monomial, map_pow, aeval_X]
    have hqa : q a ∈ idealOfVars (Fin d) A := by
      have : q a = (q a - X a) + X a := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hq a))
        (Ideal.subset_span (Set.mem_range_self a) : X a ∈ idealOfVars (Fin d) A)
    induction b with
    | zero => simp
    | succ b ih =>
      have : q a ^ (b + 1) - X a ^ (b + 1) =
          (q a ^ b - X a ^ b) * q a + X a ^ b * (q a - X a) := by ring
      rw [this]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul ih hqa
        rwa [← pow_succ] at this
      · have hXb : X a ^ b ∈ idealOfVars (Fin d) A ^ b :=
          Ideal.pow_mem_pow
            (Ideal.subset_span (Set.mem_range_self a) : X a ∈ idealOfVars (Fin d) A) b
        have := Ideal.mul_mem_mul hXb (hq a)
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this

/-- `θ_k` is injective as soon as `S/J^k` maps to `A[T]/(T)^k` sending each `t_i` to
`T_i` modulo `(T)^2`. -/
lemma theta_injective_of_lift (k : ℕ)
    (ψ : (S ⧸ RingHom.ker σ ^ k) →ₐ[A] MvPolynomial (Fin d) A ⧸ idealOfVars (Fin d) A ^ k)
    (q : Fin d → MvPolynomial (Fin d) A)
    (hψ : ∀ i, ψ (Ideal.Quotient.mk _ (t i)) = Ideal.Quotient.mk _ (q i))
    (hq : ∀ i, q i - X i ∈ idealOfVars (Fin d) A ^ 2) :
    Function.Injective (theta σ t k) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hmon : ∀ α : Fin d →₀ ℕ, ψ (Ideal.Quotient.mk _ (tpow (A := A) t α)) =
      Ideal.Quotient.mk _ (aeval q (monomial α (1 : A))) := by
    intro α
    rw [tpow, ← Ideal.Quotient.mkₐ_eq_mk A, ← AlgHom.comp_apply, comp_aeval_apply,
      ← Ideal.Quotient.mkₐ_eq_mk A, comp_aeval_apply]
    have : (fun i ↦ (ψ.comp (Ideal.Quotient.mkₐ A (RingHom.ker σ ^ k))) (t i)) =
        fun i ↦ Ideal.Quotient.mkₐ A (idealOfVars (Fin d) A ^ k) (q i) :=
      funext fun i ↦ by simpa using hψ i
    rw [this]
  set P : MvPolynomial (Fin d) A := ∑ α ∈ c.support, c α • aeval q (monomial α.1 (1 : A)) with hP
  have hPmem : P ∈ idealOfVars (Fin d) A ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : ψ (theta σ t k c) = Ideal.Quotient.mk _ P := by
      rw [theta, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, hP, map_sum]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [map_smul, hmon, ← Ideal.Quotient.mkₐ_eq_mk A, map_smul]
    rw [← this, hc, map_zero]
  by_contra hne
  obtain ⟨α₀, hα₀, hmin⟩ := c.support.exists_min_image (fun α ↦ α.1.degree)
    (Finsupp.support_nonempty_iff.mpr hne)
  have hcoeff : P.coeff α₀.1 = 0 := (mem_pow_idealOfVars_iff' _ _).mp hPmem _ α₀.2
  have hterm : ∀ α ∈ c.support, (aeval q (monomial α.1 (1 : A))).coeff α₀.1 =
      if α = α₀ then 1 else 0 := by
    intro α hα
    have h1 := (mem_pow_idealOfVars_iff' _ _).mp (aeval_monomial_sub_mem hq α.1) α₀.1
      (Nat.lt_succ_of_le (hmin α hα))
    rw [coeff_sub, sub_eq_zero] at h1
    rw [h1, coeff_monomial]
    by_cases h : α = α₀
    · simp [h]
    · have h' : ¬ (α.1 = α₀.1) := fun e ↦ h (Subtype.ext e)
      simp [h, h']
  rw [hP, coeff_sum] at hcoeff
  rw [Finset.sum_congr rfl (fun α hα ↦ by rw [coeff_smul, hterm α hα])] at hcoeff
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hα₀, ite_true]
    at hcoeff
  exact (Finsupp.mem_support_iff.mp hα₀) hcoeff

section TaylorCoeff

variable (hθ : ∀ k, Function.Bijective (theta σ t k))

/-- The truncated Taylor expansion `S → A[T]/(T)^k` in the monomial basis. -/
noncomputable def taylor (k : ℕ) : S →ₗ[A] (Mon d k →₀ A) :=
  (LinearEquiv.ofBijective (theta σ t k) (hθ k)).symm.toLinearMap ∘ₗ
    (Ideal.Quotient.mkₐ A (RingHom.ker σ ^ k)).toLinearMap

lemma theta_taylor (k : ℕ) (s : S) :
    theta σ t k (taylor σ t hθ k s) = Ideal.Quotient.mk _ s := by
  simp only [taylor, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  exact (LinearEquiv.ofBijective (theta σ t k) (hθ k)).apply_symm_apply _

lemma restr_taylor (ht : ∀ i, σ (t i) = 0) {k k' : ℕ} (h : k ≤ k') (s : S) :
    restr h (taylor σ t hθ k' s) = taylor σ t hθ k s := by
  apply (hθ k).1
  rw [theta_restr σ t ht h, theta_taylor, theta_taylor]
  rfl

/-- The Taylor coefficient of `s` at the exponent `α`. -/
noncomputable def taylorCoeff (α : Fin d →₀ ℕ) : S →ₗ[A] A :=
  Finsupp.lapply (⟨α, Nat.lt_succ_self _⟩ : Mon d (α.degree + 1)) ∘ₗ
    taylor σ t hθ (α.degree + 1)

lemma taylor_apply (ht : ∀ i, σ (t i) = 0) {k : ℕ} (α : Mon d k) (s : S) :
    taylor σ t hθ k s α = taylorCoeff σ t hθ α.1 s := by
  simp only [taylorCoeff, LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply]
  rw [← restr_taylor σ t hθ ht (Nat.succ_le_of_lt α.2), restr_apply]

/-- If all Taylor coefficients of `y ∈ S ⊗ N` vanish, then `y` lies in every `J^k (S ⊗ N)`. -/
lemma mem_pow_smul_top_of_taylorCoeff (ht : ∀ i, σ (t i) = 0) {N : Type*} [AddCommGroup N]
    [Module A N] (y : S ⊗[A] N)
    (hy : ∀ α, (taylorCoeff σ t hθ α).rTensor N y = 0) (k : ℕ) :
    y ∈ (RingHom.ker σ ^ k) • (⊤ : Submodule S (S ⊗[A] N)) := by
  let g : S →ₗ[A] S ⧸ RingHom.ker σ ^ k := (Ideal.Quotient.mkₐ A (RingHom.ker σ ^ k)).toLinearMap
  let e := LinearEquiv.ofBijective (theta σ t k) (hθ k)
  have hz' : (taylor σ t hθ k).rTensor N y = 0 := by
    apply (TensorProduct.finsuppScalarLeft A N (Mon d k)).injective
    ext α
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : Finsupp.lapply α ∘ₗ taylor σ t hθ k = taylorCoeff σ t hθ α.1 := by
      ext s
      exact taylor_apply σ t hθ ht α s
    rw [this, hy, map_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hz : g.rTensor N y = 0 := by
    have : g = e.toLinearMap ∘ₗ taylor σ t hθ k := by
      ext s
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e]
      rw [LinearEquiv.ofBijective_apply, theta_taylor]
      rfl
    rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, hz', map_zero]
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨w, rfl⟩ := (rTensor_exact N hex (Ideal.Quotient.mkₐ_surjective A _) y).mp hz
  clear hy hz' hz
  induction w with
  | tmul x n =>
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ RingHom.ker σ ^ k := by
      rw [LinearMap.mem_ker] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
    have : x ⊗ₜ[A] n = x • ((1 : S) ⊗ₜ[A] n) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hx' Submodule.mem_top
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

end TaylorCoeff

end Taylor

end Langlands.CommutativeAlgebra.IntegralFibre
