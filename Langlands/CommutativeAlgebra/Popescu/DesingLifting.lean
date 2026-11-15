import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.Popescu.DesingTools

/-! # Stacks 07CR and 07CT: the desingularization construction over a base `D` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.Desing

open MvPolynomial

section Helpers

theorem mem_map_span_singleton_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {r : R}
    {x : S} : x ∈ (Ideal.span {r}).map (algebraMap R S) ↔ ∃ y, x = algebraMap R S r * y := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [ha, mul_comm]⟩⟩

theorem aeval_sub_aeval_mem {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S)
    (u u' : ι → S) (h : ∀ i, u i - u' i ∈ I) (p : MvPolynomial ι R) :
    aeval u p - aeval u' p ∈ I := by
  rw [← Ideal.Quotient.eq]
  have : (Ideal.Quotient.mkₐ R I).comp (aeval u) = (Ideal.Quotient.mkₐ R I).comp (aeval u') := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h i)
  exact congrArg (fun φ : MvPolynomial ι R →ₐ[R] S ⧸ I ↦ φ p) this

theorem pderiv_inl_rename_inr {ι κ D : Type*} [CommRing D] (i : ι) (q : MvPolynomial κ D) :
    pderiv (Sum.inl i) (rename (Sum.inr : κ → ι ⊕ κ) q) = 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C d => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, pderiv_X]

end Helpers

section Data

/-- The substitution `y_i = ϖ² Σ_k S_ik v_k + ϖ³ w_i` of Stacks 07CR, in `D[v, w]`. -/
noncomputable def ySub {D : Type*} [CommRing D] {n c : ℕ} (ϖ : D) (S : Matrix (Fin n) (Fin c) D)
    (i : Fin n) : MvPolynomial (Fin c ⊕ Fin n) D :=
  C (ϖ ^ 2) * ∑ k, C (S i k) * X (Sum.inl k) + C (ϖ ^ 3) * X (Sum.inr i)

theorem ySub_mem {D : Type*} [CommRing D] {n c : ℕ} (ϖ : D) (S : Matrix (Fin n) (Fin c) D)
    (i : Fin n) : ySub ϖ S i ∈ Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin c ⊕ Fin n) D)} := by
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
  rw [show (C (ϖ ^ 3) : MvPolynomial (Fin c ⊕ Fin n) D) = C (ϖ ^ 2) * C ϖ by
    rw [← map_mul, ← pow_succ]]
  rw [mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The polynomial identities of Stacks 07CR over a base ring `D` with an element `ϖ`. -/
theorem exists_lift_data {R : Type*} [CommRing R] {D : Type*} [CommRing D] [Algebra R D] (ϖ : D)
    {n m c : ℕ} (hcm : c ≤ m) (f : Fin m → MvPolynomial (Fin n) R) (r : Fin n → D)
    (hfr : ∀ j, aeval r (f j) ∈ Ideal.span {ϖ ^ 4})
    (hπ : ϖ ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦
        aeval r (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j)))) ⊔
      Ideal.span {ϖ ^ 4}) :
    ∃ (S : Matrix (Fin n) (Fin c) D) (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D),
      (∀ j', aeval (fun i ↦ C (r i) + ySub ϖ S i) (f (Fin.castLE hcm j')) = C (ϖ ^ 3) * G j') ∧
      (∀ j, aeval (fun i ↦ C (r i) + ySub ϖ S i) (f j) ∈ Ideal.span {C (ϖ ^ 2)}) ∧
      (∀ j', G j' - X (Sum.inl j') ∈
        Ideal.span (Set.range fun i ↦ X (Sum.inr i)) ⊔ Ideal.span {C ϖ}) ∧
      (∀ j' k, pderiv (Sum.inl k) (G j') - (if j' = k then 1 else 0) ∈ Ideal.span {C ϖ}) := by
  classical
  -- the unit `u` with `ϖ u ∈ (minors)`
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.mp hπ
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy₂
  let M : Matrix (Fin c) (Fin n) D := fun j i ↦ aeval r (pderiv i (f (Fin.castLE hcm j)))
  have hminor : ∀ e : Fin c ↪o Fin n,
      aeval r (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j))) =
        (M.submatrix id e).det := by
    intro e
    exact (AlgHom.map_det (aeval r) _).trans rfl
  have hy₁' : y₁ ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦ (M.submatrix id e).det) := by
    simpa only [hminor] using hy₁
  obtain ⟨S, hS⟩ := exists_mul_eq_smul_one M y₁ hy₁'
  have hMS : ∀ j k, (M * S) j k = if j = k then y₁ else 0 := by
    intro j k
    rw [hS, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  set y := ySub ϖ S with hydef
  -- Taylor expansion
  have hC : ∀ p : MvPolynomial (Fin n) R,
      aeval (fun i ↦ (C (r i) : MvPolynomial (Fin c ⊕ Fin n) D)) p = C (aeval r p) := by
    intro p
    rw [show (fun i ↦ (C (r i) : MvPolynomial (Fin c ⊕ Fin n) D)) =
      (algebraMap D (MvPolynomial (Fin c ⊕ Fin n) D)) ∘ r from rfl, aeval_algebraMap_apply]
    rfl
  have hJ2 : (Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin c ⊕ Fin n) D)}) ^ 2 =
      Ideal.span {C (ϖ ^ 4)} := by
    rw [Ideal.span_singleton_pow, ← map_pow, ← pow_mul]
  have hT : ∀ j, aeval (fun i ↦ C (r i) + y i) (f j) - C (aeval r (f j)) -
      ∑ i, C (aeval r (pderiv i (f j))) * y i ∈
        Ideal.span {(C (ϖ ^ 4) : MvPolynomial (Fin c ⊕ Fin n) D)} := by
    intro j
    have := aeval_add_sub_mem (Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin c ⊕ Fin n) D)})
      (fun i ↦ C (r i)) y (fun i ↦ ySub_mem ϖ S i) (f j)
    rw [hJ2] at this
    simpa only [hC, Pi.add_def] using this
  have hy₁eq : y₁ = ϖ - t * ϖ ^ 4 := by rw [eq_sub_iff_add_eq]; exact hy
  have hsum : ∀ j', ∑ i, C (M j' i) * y i =
      C (ϖ ^ 2) * C y₁ * X (Sum.inl j') + C (ϖ ^ 3) * ∑ i, C (M j' i) * X (Sum.inr i) := by
    intro j'
    have h1 : ∀ i, C (M j' i) * y i = C (ϖ ^ 2) * ∑ k, C (M j' i * S i k) * X (Sum.inl k) +
        C (ϖ ^ 3) * (C (M j' i) * X (Sum.inr i)) := by
      intro i
      have h2 : ∑ k, C (M j' i * S i k) * X (Sum.inl k) =
          C (M j' i) * ∑ k, C (S i k) * (X (Sum.inl k) : MvPolynomial (Fin c ⊕ Fin n) D) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [map_mul, mul_assoc]
      rw [h2]
      simp only [hydef, ySub]
      ring
    have h3 : ∑ i, ∑ k, C (M j' i * S i k) * (X (Sum.inl k) : MvPolynomial (Fin c ⊕ Fin n) D) =
        C y₁ * X (Sum.inl j') := by
      rw [Finset.sum_comm]
      have : ∀ k, ∑ i, C (M j' i * S i k) * (X (Sum.inl k) : MvPolynomial (Fin c ⊕ Fin n) D) =
          C ((M * S) j' k) * X (Sum.inl k) := by
        intro k
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
      simp only [this, hMS]
      rw [Finset.sum_eq_single j']
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h3]
    ring
  have hF : ∀ j', aeval (fun i ↦ C (r i) + y i) (f (Fin.castLE hcm j')) -
      C (ϖ ^ 3) * (X (Sum.inl j') + ∑ i, C (M j' i) * X (Sum.inr i)) ∈
        Ideal.span {(C (ϖ ^ 4) : MvPolynomial (Fin c ⊕ Fin n) D)} := by
    intro j'
    have h1 := hT (Fin.castLE hcm j')
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hfr (Fin.castLE hcm j'))
    have e : aeval (fun i ↦ C (r i) + y i) (f (Fin.castLE hcm j')) -
        C (ϖ ^ 3) * (X (Sum.inl j') + ∑ i, C (M j' i) * X (Sum.inr i)) =
        (aeval (fun i ↦ C (r i) + y i) (f (Fin.castLE hcm j')) -
          C (aeval r (f (Fin.castLE hcm j'))) - ∑ i, C (M j' i) * y i) +
          C (ϖ ^ 4) * (C a - C (t * ϖ ^ 2) * X (Sum.inl j')) := by
      rw [hsum j', ← ha, hy₁eq]
      simp only [map_mul, map_sub, map_pow]
      ring
    rw [e]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  choose G'' hG'' using fun j' ↦ Ideal.mem_span_singleton'.mp (hF j')
  have hle : Ideal.span {(C (ϖ ^ 4) : MvPolynomial (Fin c ⊕ Fin n) D)} ≤
      Ideal.span {C (ϖ ^ 2)} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨C (ϖ ^ 2), by rw [← map_mul, ← pow_add]⟩
  refine ⟨S, fun j' ↦ X (Sum.inl j') + ∑ i, C (M j' i) * X (Sum.inr i) + C ϖ * G'' j',
    ?_, ?_, ?_, ?_⟩
  · intro j'
    have h := hG'' j'
    simp only [map_pow] at h ⊢
    linear_combination (-1 : MvPolynomial (Fin c ⊕ Fin n) D) * h
  · intro j
    have h1 := hT j
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hfr j)
    have e : aeval (fun i ↦ C (r i) + y i) (f j) =
        (aeval (fun i ↦ C (r i) + y i) (f j) - C (aeval r (f j)) -
          ∑ i, C (aeval r (pderiv i (f j))) * y i) + C (aeval r (f j)) +
          ∑ i, C (aeval r (pderiv i (f j))) * y i := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (hle h1) ?_)
      (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (ySub_mem ϖ S i))
    rw [← ha, map_mul]
    exact Ideal.mul_mem_left _ _ (hle (Ideal.subset_span rfl))
  · intro j'
    have e : X (Sum.inl j') + ∑ i, C (M j' i) * X (Sum.inr i) + C ϖ * G'' j' - X (Sum.inl j') =
        ∑ i, C (M j' i) * X (Sum.inr i) + C ϖ * G'' j' := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ ↦
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  · intro j' k
    have e : pderiv (Sum.inl k) (X (Sum.inl j') + ∑ i, C (M j' i) * X (Sum.inr i) +
        C ϖ * G'' j') - (if j' = k then 1 else 0) =
        C ϖ * pderiv (Sum.inl k) (G'' j') := by
      simp only [map_add, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_eq_mul, mul_zero,
        add_zero, Pi.single_apply, reduceCtorEq, ite_false, Finset.sum_const_zero,
        Sum.inl.injEq]
      split_ifs <;> simp_all [mul_comm]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end Data

section Jacobian

theorem pderiv_rename_eq_zero {ι κ D : Type*} [CommRing D] (g : κ → ι) (v : ι)
    (hv : ∀ k, g k ≠ v) (q : MvPolynomial κ D) : pderiv v (rename g q) = 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C d => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, pderiv_X, hv k]

theorem pderiv_inl_aeval {R D : Type*} [CommRing R] [CommRing D] [Algebra R D] {n κ : Type*}
    (i : n) (p : MvPolynomial n R) :
    pderiv (Sum.inl i) (aeval (fun i ↦ (X (Sum.inl i) : MvPolynomial (n ⊕ κ) D)) p) =
      aeval (fun i ↦ (X (Sum.inl i) : MvPolynomial (n ⊕ κ) D)) (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C d => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, hp,
      Pi.single_apply, Sum.inl.injEq]
    split_ifs <;> simp

theorem pderiv_inr_aeval {R D : Type*} [CommRing R] [CommRing D] [Algebra R D] {n κ : Type*}
    (k : κ) (p : MvPolynomial n R) :
    pderiv (Sum.inr k) (aeval (fun i ↦ (X (Sum.inl i) : MvPolynomial (n ⊕ κ) D)) p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C d => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k' hp => simp [hp, pderiv_X]

/-- The maximal minor of the first block of relations `(x_i − u_i, f_j(x))_{i, j < c}` of the
algebra `B` of Stacks 07CR, taken along the variables `x` and `w_{e k}`. -/
theorem det_jacobian_minor {R D : Type*} [CommRing R] [CommRing D] [Algebra R D] {n m c : ℕ}
    (hcm : c ≤ m) (f : Fin m → MvPolynomial (Fin n) R) (ϖ : D)
    (u : Fin n → MvPolynomial (Fin c ⊕ Fin n) D)
    (hu : ∀ i k, pderiv (Sum.inr k) (u i) = if i = k then C (ϖ ^ 3) else 0)
    (e : Fin c ↪o Fin n) :
    Matrix.det (Matrix.of fun i j : Fin n ⊕ Fin c ↦
      pderiv ((Sum.elim (fun i ↦ Sum.inl i) (fun k ↦ Sum.inr (Sum.inr (e k))) :
          Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n)) i)
        ((Sum.elim (fun i ↦ X (Sum.inl i) - rename Sum.inr (u i))
          (fun j' ↦ aeval (fun i ↦ X (Sum.inl i)) (f (Fin.castLE hcm j'))) :
          Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) j)) =
      C (ϖ ^ 3) ^ c * aeval (fun i ↦ (X (Sum.inl i) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D))
        (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j))) := by
  classical
  set xv : Fin n → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D := fun i ↦ X (Sum.inl i) with hxv
  let Bm : Matrix (Fin n) (Fin c) (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) :=
    Matrix.of fun i j' ↦ aeval xv (pderiv i (f (Fin.castLE hcm j')))
  let Cm : Matrix (Fin c) (Fin n) (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) :=
    Matrix.of fun k i' ↦ -(if i' = e k then C (ϖ ^ 3) else 0)
  have hM : (Matrix.of fun i j : Fin n ⊕ Fin c ↦
      pderiv ((Sum.elim (fun i ↦ Sum.inl i) (fun k ↦ Sum.inr (Sum.inr (e k))) :
          Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n)) i)
        ((Sum.elim (fun i ↦ X (Sum.inl i) - rename Sum.inr (u i))
          (fun j' ↦ aeval xv (f (Fin.castLE hcm j'))) :
          Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) j)) =
      Matrix.fromBlocks 1 Bm Cm 0 := by
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | k <;> rcases j with i' | j'
    · simp only [Matrix.of_apply, Sum.elim_inl, map_sub, pderiv_X, Matrix.fromBlocks_apply₁₁,
        Matrix.one_apply, Pi.single_apply, Sum.inl.injEq]
      rw [pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inr_ne_inl), sub_zero]
      split_ifs <;> simp_all
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Bm, hxv]
      exact pderiv_inl_aeval (D := D) (κ := Fin c ⊕ Fin n) i _
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, map_sub, pderiv_X,
        Matrix.fromBlocks_apply₂₁, Cm, Pi.single_apply, reduceCtorEq, ite_false]
      rw [pderiv_rename Sum.inr_injective, hu]
      split_ifs <;> simp
    · simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, hxv]
      exact pderiv_inr_aeval (D := D) _ _
  rw [hM, Matrix.det_fromBlocks_one₁₁, zero_sub]
  have hCB : -(Cm * Bm) = (C (ϖ ^ 3) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) • (Matrix.transpose (Matrix.of fun j k : Fin c ↦
      aeval xv (pderiv (e k) (f (Fin.castLE hcm j))))) := by
    refine Matrix.ext fun k j' ↦ ?_
    simp [Cm, Bm, Matrix.mul_apply, Finset.sum_ite_eq']
  rw [hCB, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  congr 1
  exact ((AlgHom.map_det (aeval xv) _).trans rfl).symm

/-- The Jacobian of the chart `D[x, v, w] ⧸ (x_i − u_i, G_j)` along `(x, v)`. -/
theorem det_jacobian_chart {D : Type*} [CommRing D] {n c : ℕ}
    (u : Fin n → MvPolynomial (Fin c ⊕ Fin n) D) (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D) :
    Matrix.det (Matrix.of fun i j : Fin n ⊕ Fin c ↦
      pderiv ((Sum.elim (fun i ↦ Sum.inl i) (fun k ↦ Sum.inr (Sum.inl k)) :
          Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n)) i)
        ((Sum.elim (fun i ↦ X (Sum.inl i) - rename Sum.inr (u i)) (fun j' ↦ rename Sum.inr (G j')) :
          Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) j)) =
      Matrix.det (Matrix.of fun k j' : Fin c ↦ rename Sum.inr (pderiv (Sum.inl k) (G j'))) := by
  classical
  let Cm : Matrix (Fin c) (Fin n) (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) :=
    Matrix.of fun k i' ↦ pderiv (Sum.inr (Sum.inl k)) (X (Sum.inl i') - rename Sum.inr (u i'))
  have hM : (Matrix.of fun i j : Fin n ⊕ Fin c ↦
      pderiv ((Sum.elim (fun i ↦ Sum.inl i) (fun k ↦ Sum.inr (Sum.inl k)) :
          Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n)) i)
        ((Sum.elim (fun i ↦ X (Sum.inl i) - rename Sum.inr (u i)) (fun j' ↦ rename Sum.inr (G j')) :
          Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) j)) =
      Matrix.fromBlocks 1 0 Cm
        (Matrix.of fun k j' : Fin c ↦ rename Sum.inr (pderiv (Sum.inl k) (G j'))) := by
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | k <;> rcases j with i' | j'
    · simp only [Matrix.of_apply, Sum.elim_inl, map_sub, pderiv_X, Matrix.fromBlocks_apply₁₁,
        Matrix.one_apply, Pi.single_apply, Sum.inl.injEq]
      rw [pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inr_ne_inl), sub_zero]
      split_ifs <;> simp_all
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
      exact pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inr_ne_inl) _
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Cm]
    · simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
      exact pderiv_rename Sum.inr_injective _ _
  rw [hM, Matrix.det_fromBlocks_one₁₁, Matrix.mul_zero, sub_zero]

end Jacobian

section Construction

variable {R D : Type*} [CommRing R] [CommRing D] [Algebra R D] {n m c : ℕ}

/-- The relations `x_i − (r_i + y_i)` of the algebra `B` of Stacks 07CR. -/
noncomputable def relH (r : Fin n → D) (ϖ : D) (S : Matrix (Fin n) (Fin c) D) (i : Fin n) :
    MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
  X (Sum.inl i) - rename Sum.inr (C (r i) + ySub ϖ S i)

/-- The relations `f_j(x)` of the algebra `B` of Stacks 07CR. -/
noncomputable def relF (f : Fin m → MvPolynomial (Fin n) R) (j : Fin m) :
    MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
  aeval (fun i ↦ X (Sum.inl i)) (f j)

/-- The relations `g_j(v, w)` of the algebra `B` of Stacks 07CR. -/
noncomputable def relG (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D) (j : Fin c) :
    MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
  rename Sum.inr (G j)

/-- The ideal of the algebra `B` of Stacks 07CR, split as needed for `isSmoothAt_of_strictlyStandard`. -/
noncomputable abbrev idealB (hcm : c ≤ m) (f : Fin m → MvPolynomial (Fin n) R) (r : Fin n → D) (ϖ : D)
    (S : Matrix (Fin n) (Fin c) D) (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D) :
    Ideal (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) :=
  Ideal.span (Set.range (Sum.elim (relH r ϖ S) (fun j' ↦ relF (D := D) f (Fin.castLE hcm j')))) ⊔
    Ideal.span (Set.range (Sum.elim (relF f) (relG G)))

/-- The ideal of the smooth chart `B'` of Stacks 07CR. -/
noncomputable abbrev idealB' (r : Fin n → D) (ϖ : D) (S : Matrix (Fin n) (Fin c) D)
    (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D) : Ideal (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) :=
  Ideal.span (Set.range (Sum.elim (relH r ϖ S) (relG G)))

theorem pderiv_inr_u (r : Fin n → D) (ϖ : D) (S : Matrix (Fin n) (Fin c) D) (i k : Fin n) :
    pderiv (Sum.inr k) (C (r i) + ySub ϖ S i) = if i = k then C (ϖ ^ 3) else 0 := by
  classical
  simp only [ySub, map_add, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, smul_eq_mul,
    Pi.single_apply, reduceCtorEq, ite_false, mul_zero, add_zero, Finset.sum_const_zero,
    zero_add, Sum.inr.injEq]
  split_ifs <;> simp_all

theorem rename_aeval (u : Fin n → MvPolynomial (Fin c ⊕ Fin n) D) (p : MvPolynomial (Fin n) R) :
    rename Sum.inr (aeval u p) =
      aeval (fun i ↦ (rename Sum.inr (u i) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)) p :=
  (AlgHom.congr_fun (MvPolynomial.comp_aeval u ((rename (R := D) Sum.inr).restrictScalars R)) p :)

/-- `f_j(x) ≡ f_j(r + y)` modulo the relations `x_i − (r_i + y_i)`. -/
theorem relF_sub_mem (f : Fin m → MvPolynomial (Fin n) R) (r : Fin n → D) (ϖ : D)
    (S : Matrix (Fin n) (Fin c) D) (j : Fin m) :
    relF (D := D) f j - rename Sum.inr (aeval (fun i ↦ C (r i) + ySub ϖ S i) (f j)) ∈
      Ideal.span (Set.range (relH r ϖ S)) := by
  rw [rename_aeval]
  exact aeval_sub_aeval_mem (Ideal.span (Set.range (relH r ϖ S))) (fun i ↦ X (Sum.inl i))
    (fun i ↦ rename Sum.inr (C (r i) + ySub ϖ S i))
    (fun i ↦ Ideal.subset_span (Set.mem_range_self i)) (f j)

end Construction

section Charts

/-- Stacks 07CR, away from `π`: the algebra `B` is smooth over `D` at every prime not containing
`π`, because `π` is strictly standard for its presentation (Stacks 07CA). -/
theorem isSmoothAt_B_of_notMem {R : Type*} [CommRing R] {D : Type u} [CommRing D] [Algebra R D]
    {n m c : ℕ} (π : R) (ϖ : D) (hπϖ : algebraMap R D π = ϖ) (hcm : c ≤ m)
    (f : Fin m → MvPolynomial (Fin n) R) (r : Fin n → D)
    (S : Matrix (Fin n) (Fin c) D) (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D)
    (hFG : ∀ j', aeval (fun i ↦ C (r i) + ySub ϖ S i) (f (Fin.castLE hcm j')) = C (ϖ ^ 3) * G j')
    (hs1 : C π ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦
        Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j))) ⊔
      Ideal.span (Set.range f))
    (hs2 : ∀ j, C π * f j ∈
      Ideal.span (Set.range fun j' ↦ f (Fin.castLE hcm j')) ⊔ Ideal.span (Set.range f) ^ 2)
    (q : Ideal (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ idealB hcm f r ϖ S G)) [q.IsPrime]
    (hq : Ideal.Quotient.mk _ (C ϖ) ∉ q) : Algebra.IsSmoothAt D q := by
  classical
  let xv : Fin n → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D := fun i ↦ X (Sum.inl i)
  let F₁ : Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
    Sum.elim (relH r ϖ S) (fun j' ↦ relF (D := D) f (Fin.castLE hcm j'))
  let F₂ : Fin m ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
    Sum.elim (relF f) (relG G)
  let K := idealB hcm f r ϖ S G
  have hK' : K = Ideal.span (Set.range F₁) ⊔ Ideal.span (Set.range F₂) := rfl
  have hCπ : aeval xv (C π : MvPolynomial (Fin n) R) =
      (C ϖ : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) := by
    rw [aeval_C, MvPolynomial.algebraMap_apply, hπϖ]
  have hFK : ∀ j, relF (D := D) (c := c) f j ∈ K :=
    fun j ↦ Ideal.mem_sup_right (Ideal.subset_span ⟨Sum.inl j, rfl⟩)
  set a : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D := C ϖ ^ (3 * c + 3) with ha_def
  have ha : a ∈ Ideal.span (Set.range fun μ : {μ : Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n) //
      Function.Injective μ} ↦ Matrix.det fun i j : Fin n ⊕ Fin c ↦ pderiv (μ.1 i) (F₁ j)) ⊔ K := by
    set Jμ := Ideal.span (Set.range fun μ : {μ : Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n) //
      Function.Injective μ} ↦ Matrix.det fun i j : Fin n ⊕ Fin c ↦ pderiv (μ.1 i) (F₁ j))
    have h1 := Ideal.mem_map_of_mem (aeval xv) hs1
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, hCπ] at h1
    obtain ⟨y, hy, k, hk, hyk⟩ := Submodule.mem_sup.mp h1
    have hyμ : (C (ϖ ^ 3)) ^ c * y ∈ Jμ := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
        have hinj : Function.Injective (Sum.elim (fun i ↦ Sum.inl i)
            (fun k ↦ Sum.inr (Sum.inr (e k))) : Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n)) :=
          Function.Injective.sumElim Sum.inl_injective
            (Sum.inr_injective.comp (Sum.inr_injective.comp e.injective))
            (fun _ _ ↦ Sum.inl_ne_inr)
        refine Ideal.subset_span ⟨⟨_, hinj⟩, ?_⟩
        exact det_jacobian_minor hcm f ϖ (fun i ↦ C (r i) + ySub ϖ S i) (pderiv_inr_u r ϖ S) e
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Ideal.add_mem _ hx hy
      · intro b x _ hx
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hx
    have hkK : k ∈ K := by
      refine (Ideal.span_le.mpr ?_) hk
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact hFK j
    have e : a = C (ϖ ^ 2) * ((C (ϖ ^ 3)) ^ c * (y + k)) := by
      rw [hyk, ha_def]
      simp only [map_pow]
      ring
    rw [e, mul_add, mul_add]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hyμ))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hkK)))
  have ha₂ : ∀ t, a * F₂ t ∈ Ideal.span (Set.range F₁) ⊔ K ^ 2 := by
    rintro (j | j')
    · have h2 := Ideal.mem_map_of_mem (aeval xv) (hs2 j)
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, map_mul, hCπ] at h2
      have hle : Ideal.span (aeval xv '' Set.range fun j' ↦ f (Fin.castLE hcm j')) ⊔
          Ideal.span (aeval xv '' Set.range f) ^ 2 ≤ Ideal.span (Set.range F₁) ⊔ K ^ 2 := by
        refine sup_le_sup ?_ (Ideal.pow_right_mono ?_ 2)
        · rw [Ideal.span_le]
          rintro _ ⟨_, ⟨j', rfl⟩, rfl⟩
          exact Ideal.subset_span ⟨Sum.inr j', rfl⟩
        · rw [Ideal.span_le]
          rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
          exact hFK j
      have e : a * F₂ (Sum.inl j) = C ϖ ^ (3 * c + 2) * (C ϖ * aeval xv (f j)) := by
        simp only [ha_def, F₂, Sum.elim_inl, relF, xv]
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (hle h2)
    · have h3 : C (ϖ ^ 3) * relG G j' ∈ Ideal.span (Set.range F₁) := by
        have e1 : C (ϖ ^ 3) * relG G j' = relF (D := D) (c := c) f (Fin.castLE hcm j') -
            (relF f (Fin.castLE hcm j') - rename Sum.inr
              (aeval (fun i ↦ C (r i) + ySub ϖ S i) (f (Fin.castLE hcm j')))) := by
          rw [hFG j', relG, map_mul, rename_C]
          ring
        rw [e1]
        refine Ideal.sub_mem _ (Ideal.subset_span ⟨Sum.inr j', rfl⟩) ?_
        refine (Ideal.span_mono ?_) (relF_sub_mem f r ϖ S _)
        rintro _ ⟨i, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
      have e : a * F₂ (Sum.inr j') = C ϖ ^ (3 * c) * (C (ϖ ^ 3) * relG G j') := by
        simp only [ha_def, F₂, Sum.elim_inr, map_pow]
        ring
      rw [e]
      exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ h3)
  have hq' : Ideal.Quotient.mk K a ∉ q := by
    rw [ha_def, map_pow]
    exact fun h ↦ hq (‹q.IsPrime›.mem_of_pow_mem _ h)
  exact isSmoothAt_of_strictlyStandard F₁ F₂ K hK' a ha ha₂ q hq'

/-- Stacks 07CR, the chart `B' = D[x, v, w] ⧸ (x_i − (r_i + y_i), g_j)`: it is smooth over `D` at
every prime containing `ϖ`, as its Jacobian along `(x, v)` is `≡ 1` modulo `ϖ`. -/
theorem isSmoothAt_B'_of_mem {D : Type u} [CommRing D] {n c : ℕ} (r : Fin n → D) (ϖ : D)
    (S : Matrix (Fin n) (Fin c) D) (G : Fin c → MvPolynomial (Fin c ⊕ Fin n) D)
    (hG4 : ∀ j' k, pderiv (Sum.inl k) (G j') - (if j' = k then 1 else 0) ∈ Ideal.span {C ϖ})
    (q : Ideal (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ idealB' r ϖ S G)) [q.IsPrime]
    (hq : Ideal.Quotient.mk _ (C ϖ) ∈ q) : Algebra.IsSmoothAt D q := by
  classical
  let v : Fin n ⊕ Fin c → MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D :=
    Sum.elim (relH r ϖ S) (relG G)
  let μ : Fin n ⊕ Fin c → Fin n ⊕ (Fin c ⊕ Fin n) :=
    Sum.elim (fun i ↦ Sum.inl i) (fun k ↦ Sum.inr (Sum.inl k))
  have hμ : Function.Injective μ := Function.Injective.sumElim Sum.inl_injective
    (Sum.inr_injective.comp Sum.inl_injective) (fun _ _ ↦ Sum.inl_ne_inr)
  have hstd := isStandardSmooth_away_det_mul v μ hμ 1
  set d := Matrix.det fun i j : Fin n ⊕ Fin c ↦ pderiv (μ i) (v j) with hd_def
  have hd : d = Matrix.det (Matrix.of fun k j' : Fin c ↦
      (rename Sum.inr (pderiv (Sum.inl k) (G j')) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)) :=
    det_jacobian_chart (fun i ↦ C (r i) + ySub ϖ S i) G
  have hd1 : d - 1 ∈ Ideal.span {(C ϖ : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)} := by
    rw [hd, ← Ideal.Quotient.eq,
      RingHom.map_det (S := MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸
        Ideal.span {(C ϖ : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)}) (Ideal.Quotient.mk _)]
    have hone : (Ideal.Quotient.mk (Ideal.span {(C ϖ : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)})).mapMatrix
        (Matrix.of fun k j' : Fin c ↦
          (rename Sum.inr (pderiv (Sum.inl k) (G j')) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D)) =
        1 := by
      refine Matrix.ext fun k j' ↦ ?_
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
      have h := Ideal.mem_map_of_mem
        (rename (R := D) Sum.inr : MvPolynomial (Fin c ⊕ Fin n) D →ₐ[D]
          MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D) (hG4 j' k)
      rw [Ideal.map_span, Set.image_singleton, rename_C, map_sub] at h
      rw [Ideal.Quotient.eq.mpr h]
      by_cases hk : j' = k
      · subst hk
        simp
      · simp [hk, Ne.symm hk]
    rw [hone, Matrix.det_one]
    exact (map_one _).symm
  have hFP : Algebra.FinitePresentation D (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸
      idealB' r ϖ S G) := Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  refine isSmoothAt_of_smooth_away (inferInstance : Algebra.Smooth D (Localization.Away
    (Ideal.Quotient.mk (Ideal.span (Set.range v)) d * 1))) q ?_
  rw [mul_one]
  intro hdq
  have h1 : Ideal.Quotient.mk (idealB' r ϖ S G) (d - 1) ∈ q := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hd1
    rw [← hy, map_mul]
    exact Ideal.mul_mem_left _ _ hq
  rw [map_sub, map_one] at h1
  apply ‹q.IsPrime›.ne_top
  rw [Ideal.eq_top_iff_one]
  have := q.sub_mem hdq h1
  rwa [sub_sub_cancel] at this

end Charts

section Main

/-- `H(rename inr q)` for an `aevalTower` map out of `D[x, v, w]`. -/
theorem aevalTower_rename_inr {R D Λ : Type*} [CommRing R] [CommRing D] [CommRing Λ] [Algebra R D]
    [Algebra R Λ] {n c : ℕ} (ψ : D →ₐ[R] Λ) (val : Fin n ⊕ (Fin c ⊕ Fin n) → Λ)
    (q : MvPolynomial (Fin c ⊕ Fin n) D) :
    aevalTower ψ val (rename Sum.inr q) = aevalTower ψ (fun v ↦ val (Sum.inr v)) q := by
  induction q using MvPolynomial.induction_on with
  | C d => simp [aevalTower_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, aevalTower_X]

/-- Stacks 07CR and 07CT combined, over a finitely presented `R`-algebra `D`: from a strictly
standard `π` in `A` and a map `A → D ⧸ π⁴D` compatible with `A → Λ` and `D → Λ`, build a finitely
presented `B` with maps `A → B`, `D → B`, `B → Λ`, smooth over `R` away from `π` if `D` is, and smooth
over `R` at every prime over `π` coming from `Λ` above which `D` is smooth over `R`. -/
theorem exists_desing_lift {R : Type u} [CommRing R] (π : R)
    (hR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ]
    (hΛ : ∀ x : Λ, algebraMap R Λ π ^ 2 * x = 0 → algebraMap R Λ π * x = 0)
    {A : Type u} [CommRing A] [Algebra R A] (hA : IsStrictlyStandard R (algebraMap R A π))
    {D : Type u} [CommRing D] [Algebra R D] [Algebra.FinitePresentation R D]
    (fA : A →ₐ[R] Λ) (ψ : D →ₐ[R] Λ)
    (σ : A →ₐ[R] D ⧸ Ideal.span {algebraMap R D (π ^ 4)})
    (hσ : ∀ (a : A) (d : D), σ a = Ideal.Quotient.mk _ d →
      ∃ z : Λ, fA a - ψ d = algebraMap R Λ (π ^ 4) * z) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.FinitePresentation R B ∧
      ∃ (g : A →ₐ[R] B) (j : D →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = fA ∧ h.comp j = ψ ∧
        (Algebra.Smooth R (Localization.Away (algebraMap R D π)) →
          Algebra.Smooth R (Localization.Away (algebraMap R B π))) ∧
        ∀ (𝔭 : Ideal Λ) [𝔭.IsPrime], algebraMap R Λ π ∈ 𝔭 →
          Algebra.IsSmoothAt R (𝔭.comap ψ) → Algebra.IsSmoothAt R (𝔭.comap h) := by
  classical
  obtain ⟨n, m, c, -, hcm, f, φ, hφ, hker, hmin, g₀, hg₀, hg₀f⟩ := hA
  obtain ⟨ϖ, hπϖ⟩ : ∃ ϖ : D, algebraMap R D π = ϖ := ⟨_, rfl⟩
  have hI4 : Ideal.span {algebraMap R D (π ^ 4)} = Ideal.span {ϖ ^ 4} := by rw [map_pow, hπϖ]
  -- lifts of the section and its compatibility
  choose r hr using fun i ↦ Ideal.Quotient.mk_surjective (σ (φ (X i)))
  have hσφ : ∀ p, σ (φ p) = Ideal.Quotient.mk _ (aeval r p) := by
    intro p
    have : σ.comp φ = (Ideal.Quotient.mkₐ R _).comp (aeval r) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk, hr]
    exact AlgHom.congr_fun this p
  have hfker : ∀ j, φ (f j) = 0 := fun j ↦ by
    have : f j ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨j, rfl⟩
    exact this
  have hfr : ∀ j, aeval r (f j) ∈ Ideal.span {ϖ ^ 4} := by
    intro j
    rw [← hI4, ← Ideal.Quotient.eq_zero_iff_mem, ← hσφ, hfker, map_zero]
  have hπmin : ϖ ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦
      aeval r (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j)))) ⊔
      Ideal.span {ϖ ^ 4} := by
    have h1 := Ideal.mem_map_of_mem σ hmin
    rw [Ideal.map_span, AlgHom.commutes, ← Set.range_comp] at h1
    have h2 : (⇑σ ∘ fun e : Fin c ↪o Fin n ↦
        φ (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j)))) =
        ⇑(Ideal.Quotient.mk (Ideal.span {algebraMap R D (π ^ 4)})) ∘ fun e : Fin c ↪o Fin n ↦
          aeval r (Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j))) := by
      funext e
      exact hσφ _
    rw [h2, Set.range_comp, ← Ideal.map_span] at h1
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have h3 : ϖ - y ∈ Ideal.span {ϖ ^ 4} := by
      rw [← hI4, ← Ideal.Quotient.eq, hyx, ← hπϖ, Ideal.Quotient.mk_algebraMap]
    have := Ideal.add_mem _ (Ideal.mem_sup_left (T := Ideal.span {ϖ ^ 4}) hy)
      (Ideal.mem_sup_right h3)
    rwa [add_sub_cancel] at this
  obtain ⟨S, G, hFG, hF2, hG5, hG4⟩ := exists_lift_data ϖ hcm f r hfr hπmin
  choose lam' hlam' using fun i ↦ hσ (φ (X i)) (r i) (hr i).symm
  -- strictly standard data in `R[x]`
  have hφC : φ (C π) = algebraMap R A π := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes π
  have hs1 : (C π : MvPolynomial (Fin n) R) ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦
      Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j))) ⊔
      Ideal.span (Set.range f) := by
    have h1 : algebraMap R A π ∈ (Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦
        Matrix.det fun j k : Fin c ↦ pderiv (e k) (f (Fin.castLE hcm j)))).map φ := by
      rw [Ideal.map_span, ← Set.range_comp]
      exact hmin
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ hφ).mp h1
    have h2 : C π - y ∈ Ideal.span (Set.range f) := by
      rw [← hker, RingHom.mem_ker, map_sub, hyx, hφC, sub_self]
    have := Ideal.add_mem _ (Ideal.mem_sup_left (T := Ideal.span (Set.range f)) hy)
      (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at this
  have hCg : (C π : MvPolynomial (Fin n) R) - g₀ ∈ Ideal.span (Set.range f) := by
    rw [← hker, RingHom.mem_ker, map_sub, hφC, hg₀, sub_self]
  have hs2 : ∀ j, (C π : MvPolynomial (Fin n) R) * f j ∈
      Ideal.span (Set.range fun j' ↦ f (Fin.castLE hcm j')) ⊔ Ideal.span (Set.range f) ^ 2 := by
    intro j
    have hfj : f j ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨j, rfl⟩
    have himg : Ideal.span (f '' {i : Fin m | (i : ℕ) < c}) ≤
        Ideal.span (Set.range fun j' ↦ f (Fin.castLE hcm j')) := by
      apply Ideal.span_mono
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    by_cases hj : c ≤ (j : ℕ)
    · have e : C π * f j = g₀ * f j + (C π - g₀) * f j := by ring
      rw [e]
      refine Ideal.add_mem _ ((sup_le_sup_right himg _) (hg₀f j hj)) (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hCg hfj
    · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨⟨j, not_le.mp hj⟩, rfl⟩))
  -- the map `H : D[x, v, w] → Λ`, `x ↦ λ`, `v ↦ 0`, `w ↦ π λ'`
  have hψϖ : ψ ϖ = algebraMap R Λ π := by rw [← hπϖ, AlgHom.commutes]
  let val : Fin n ⊕ (Fin c ⊕ Fin n) → Λ :=
    Sum.elim (fun i ↦ fA (φ (X i))) (Sum.elim (fun _ ↦ 0) (fun i ↦ algebraMap R Λ π * lam' i))
  let H : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D →ₐ[R] Λ := aevalTower ψ val
  have hHC : ∀ d, H (C d) = ψ d := fun d ↦ aevalTower_C _ _ _
  have hHX : ∀ v, H (X v) = val v := fun v ↦ aevalTower_X _ _ _
  have hHF : ∀ p : MvPolynomial (Fin n) R,
      H (aeval (fun i ↦ X (Sum.inl i)) p) = fA (φ p) := by
    intro p
    have : H.comp (aeval fun i ↦ X (Sum.inl i)) = fA.comp φ := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, aeval_X, hHX, AlgHom.comp_apply]
      rfl
    exact AlgHom.congr_fun this p
  have hHu : ∀ i, H (rename Sum.inr (C (r i) + ySub ϖ S i)) =
      ψ (r i) + algebraMap R Λ (π ^ 4) * lam' i := by
    intro i
    rw [aevalTower_rename_inr]
    simp only [ySub, map_add, map_mul, map_sum, aevalTower_C, aevalTower_X, val, Sum.elim_inl,
      Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add, map_pow, hψϖ]
    ring
  have hHrelH : ∀ i, H (relH r ϖ S i) = 0 := by
    intro i
    rw [relH, map_sub, hHu, hHX]
    simp only [val, Sum.elim_inl]
    rw [← hlam' i]
    ring
  have hHrelF : ∀ j, H (relF f j) = 0 := fun j ↦ by rw [relF, hHF, hfker, map_zero]
  have hHspanH : Ideal.span (Set.range (relH r ϖ S)) ≤ RingHom.ker H := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hHrelH i
  have hHrelG : ∀ j', H (relG G j') = 0 := by
    intro j'
    have h3 : algebraMap R Λ π ^ 3 * H (relG G j') = 0 := by
      have h0 := hHspanH (relF_sub_mem f r ϖ S (Fin.castLE hcm j'))
      rw [RingHom.mem_ker, map_sub, hHrelF, zero_sub, neg_eq_zero, hFG j', map_mul, rename_C,
        map_mul, hHC, map_pow, hψϖ] at h0
      exact h0
    have h4 : H (relG G j') ∈ Ideal.span {algebraMap R Λ π} := by
      let H' : MvPolynomial (Fin c ⊕ Fin n) D →ₐ[R] Λ := aevalTower ψ (fun v ↦ val (Sum.inr v))
      have hle : Ideal.span (Set.range fun i ↦ (X (Sum.inr i) : MvPolynomial (Fin c ⊕ Fin n) D)) ⊔
          Ideal.span {C ϖ} ≤ (Ideal.span {algebraMap R Λ π}).comap H' := by
        refine sup_le ?_ ?_
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          show H' (X (Sum.inr i)) ∈ Ideal.span {algebraMap R Λ π}
          rw [show H' (X (Sum.inr i)) = algebraMap R Λ π * lam' i from aevalTower_X _ _ _]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          rw [SetLike.mem_coe, Ideal.mem_comap,
            show H' (C ϖ) = ψ ϖ from aevalTower_C _ _ _, hψϖ]
          exact Ideal.subset_span rfl
      have h6 := hle (hG5 j')
      rw [Ideal.mem_comap, map_sub, show H' (X (Sum.inl j')) = 0 from aevalTower_X _ _ _,
        sub_zero] at h6
      have : H (relG G j') = H' (G j') := aevalTower_rename_inr ψ val (G j')
      rw [this]
      exact h6
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h4
    rw [← hz] at h3 ⊢
    have h7 : algebraMap R Λ π ^ (3 + 1) • z = 0 := by
      rw [smul_eq_mul]
      linear_combination h3
    have := smul_eq_zero_of_pow_smul_eq_zero (R := Λ) (M := Λ) (π := algebraMap R Λ π)
      (fun y hy ↦ hΛ y hy) 3 h7
    rw [smul_eq_mul] at this
    rw [mul_comm]
    exact this
  have hKH : idealB hcm f r ϖ S G ≤ RingHom.ker H := by
    refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
    · rintro _ ⟨(i | j'), rfl⟩
      · exact hHrelH i
      · exact hHrelF _
    · rintro _ ⟨(j | j'), rfl⟩
      · exact hHrelF j
      · exact hHrelG j'
  -- the algebra `B` and its maps
  let K := idealB hcm f r ϖ S G
  let h : (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K) →ₐ[R] Λ :=
    Ideal.Quotient.liftₐ K H (fun a ha ↦ hKH ha)
  have hh : ∀ x, h (Ideal.Quotient.mk K x) = H x := fun _ ↦ rfl
  have hspanf : Ideal.span (Set.range f) ≤ RingHom.ker ((Ideal.Quotient.mkₐ R K).comp
      (aeval fun i ↦ (X (Sum.inl i) : MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D))) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨Sum.inl j, rfl⟩)
  let g : A →ₐ[R] MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K :=
    AlgHom.liftOfSurjective φ hφ ((Ideal.Quotient.mkₐ R K).comp
      (aeval fun i ↦ X (Sum.inl i))) (fun x hx ↦ hspanf (by rw [← hker]; exact hx))
  have hg : ∀ p, g (φ p) = Ideal.Quotient.mk K (aeval (fun i ↦ X (Sum.inl i)) p) :=
    fun p ↦ AlgHom.liftOfSurjective_apply _ _ _ _ p
  have hKfg : K.FG := (Submodule.fg_span (Set.finite_range _)).sup
    (Submodule.fg_span (Set.finite_range _))
  have hFPD : Algebra.FinitePresentation D (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K) :=
    Algebra.FinitePresentation.quotient hKfg
  have hFPB : Algebra.FinitePresentation R (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K) :=
    Algebra.FinitePresentation.trans R D _
  have hπB : algebraMap R (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K) π =
      Ideal.Quotient.mk K (C ϖ) := by
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_apply, hπϖ]
  refine ⟨_, inferInstance, inferInstance, hFPB, g, IsScalarTower.toAlgHom R D _, h, ?_, ?_, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hφ a
    rw [AlgHom.comp_apply, hg, hh, hHF]
  · apply AlgHom.ext
    intro d
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← Ideal.Quotient.mk_algebraMap, hh,
      MvPolynomial.algebraMap_eq, hHC]
  · intro hDπ
    apply smooth_away_of_isSmoothAt
    intro q _ hq
    rw [hπB] at hq
    have h1 := isSmoothAt_B_of_notMem π ϖ hπϖ hcm f r S G hFG hs1 hs2 q hq
    have h2 : Algebra.IsSmoothAt R (q.under D) := by
      refine isSmoothAt_of_smooth_away hDπ (q.under D) ?_
      rw [Ideal.under, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply, hπB]
      exact hq
    exact isSmoothAt_trans q h1 h2
  · intro 𝔭 _ hπ𝔭 hψ𝔭
    let K' := idealB' r ϖ S G
    have hK'K : K' ≤ K := by
      rw [Ideal.span_le]
      rintro _ ⟨(i | j'), rfl⟩
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨Sum.inl i, rfl⟩)
      · exact Ideal.mem_sup_right (Ideal.subset_span ⟨Sum.inr j', rfl⟩)
    let p' : (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K') →ₐ[R]
        MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K := Ideal.Quotient.factorₐ R hK'K
    have hp' : ∀ x, p' (Ideal.Quotient.mk K' x) = Ideal.Quotient.mk K x := fun _ ↦ rfl
    have hp'surj : Function.Surjective p' := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨_, hp' x⟩
    let 𝔮 := 𝔭.comap h
    let 𝔮' := 𝔮.comap p'
    have hx𝔮' : Ideal.Quotient.mk K' (C ϖ) ∈ 𝔮' := by
      show h (p' (Ideal.Quotient.mk K' (C ϖ))) ∈ 𝔭
      rw [hp', hh, hHC, hψϖ]
      exact hπ𝔭
    have hD𝔮' : Algebra.IsSmoothAt D 𝔮' := isSmoothAt_B'_of_mem r ϖ S G hG4 𝔮' hx𝔮'
    have hunder : 𝔮'.under D = 𝔭.comap ψ := by
      ext d
      show h (p' (algebraMap D _ d)) ∈ 𝔭 ↔ ψ d ∈ 𝔭
      rw [← Ideal.Quotient.mk_algebraMap, hp', hh, MvPolynomial.algebraMap_eq, hHC]
    have hR𝔮' : Algebra.IsSmoothAt R 𝔮' := isSmoothAt_trans 𝔮' hD𝔮' (by convert hψ𝔭)
    have hFPD' : Algebra.FinitePresentation D (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K') :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
    have hFPB' : Algebra.FinitePresentation R (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K') :=
      Algebra.FinitePresentation.trans R D _
    have := hR𝔮'
    obtain ⟨t, ht, hts⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R 𝔮'
    -- Nakayama for the ideal generated by the `f_j(x)` in `B'`
    obtain ⟨x', hx'⟩ : ∃ x', Ideal.Quotient.mk K' (C ϖ) = x' := ⟨_, rfl⟩
    let N : Ideal (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K') :=
      Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk K' (relF (D := D) (c := c) f j))
    have hHK' : Ideal.span (Set.range (relH r ϖ S)) ≤ K' := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
    have hmod : ∀ j, Ideal.Quotient.mk K' (relF (D := D) (c := c) f j) =
        Ideal.Quotient.mk K' (rename Sum.inr (aeval (fun i ↦ C (r i) + ySub ϖ S i) (f j))) :=
      fun j ↦ Ideal.Quotient.eq.mpr (hHK' (relF_sub_mem f r ϖ S j))
    have hn1 : ∀ j, Ideal.Quotient.mk K' (relF (D := D) (c := c) f j) ∈ Ideal.span {x' ^ 2} := by
      intro j
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hF2 j)
      rw [hmod, ← hy, map_mul, rename_C, map_mul, ← hx', map_pow, map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    have hn2 : ∀ j', Ideal.Quotient.mk K' (relF (D := D) (c := c) f (Fin.castLE hcm j')) = 0 := by
      intro j'
      rw [hmod, hFG j', map_mul, rename_C, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (show rename Sum.inr (G j') ∈ K' from
          Ideal.subset_span ⟨Sum.inr j', rfl⟩), mul_zero]
    have hn3 : ∀ j, x' * Ideal.Quotient.mk K' (relF (D := D) (c := c) f j) ∈ N ^ 2 := by
      intro j
      let ψ' : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K' :=
        (Ideal.Quotient.mkₐ R K').comp (aeval fun i ↦ X (Sum.inl i))
      have h1 := Ideal.mem_map_of_mem ψ' (hs2 j)
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, map_mul] at h1
      have hψ'C : ψ' (C π) = x' := by
        rw [← hx']
        show Ideal.Quotient.mk K' (aeval _ (C π)) = _
        rw [aeval_C, MvPolynomial.algebraMap_apply, hπϖ]
      have hψ'f : ∀ j, ψ' (f j) = Ideal.Quotient.mk K' (relF (D := D) (c := c) f j) :=
        fun j ↦ rfl
      rw [hψ'C, hψ'f] at h1
      have hA : Ideal.span (ψ' '' Set.range fun j' ↦ f (Fin.castLE hcm j')) ≤ N ^ 2 := by
        rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j', rfl⟩, rfl⟩
        rw [SetLike.mem_coe, hψ'f, hn2]
        exact Ideal.zero_mem _
      have hB : Ideal.span (ψ' '' Set.range f) = N := by
        rw [← Set.range_comp]
        rfl
      rw [hB] at h1
      exact (sup_le hA le_rfl) h1
    let M := Ideal.span {x'} * N
    have hNle : N ≤ Ideal.span {x' ^ 2} := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hn1 j
    have hMN2 : M ≤ N ^ 2 := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨j, rfl⟩
        exact hn3 j
      · rw [mul_zero]
        exact Ideal.zero_mem _
      · intro a b _ _ ha hb
        rw [mul_add]
        exact Ideal.add_mem _ ha hb
      · intro a b _ hb
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hb
    have hMle : M ≤ Ideal.span {x'} • M := by
      rw [Ideal.smul_eq_mul]
      calc M ≤ N ^ 2 := hMN2
        _ = N * N := pow_two N
        _ ≤ Ideal.span {x' ^ 2} * N := Ideal.mul_mono_left hNle
        _ = Ideal.span {x'} * M := by
          rw [pow_two, ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    have hMfg : M.FG := Ideal.FG.mul (Submodule.fg_span_singleton x')
      (Submodule.fg_span (Set.finite_range _))
    obtain ⟨r₀, hr₀, hr₀M⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (Ideal.span {x'}) M hMfg hMle
    have hx'𝔮 : x' ∈ 𝔮' := hx' ▸ hx𝔮'
    have hr₀𝔮 : r₀ ∉ 𝔮' := by
      intro hr
      have h1 : r₀ - 1 ∈ 𝔮' := (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx'𝔮)) hr₀
      have := 𝔮'.sub_mem hr h1
      rw [sub_sub_cancel] at this
      exact Ideal.IsPrime.ne_top (inferInstance : 𝔮'.IsPrime) ((Ideal.eq_top_iff_one _).mpr this)
    -- localize at `t * r₀`
    let s := t * r₀
    have hs𝔮 : s ∉ 𝔮' := (inferInstance : 𝔮'.IsPrime).mul_notMem ht hr₀𝔮
    have hsm : Algebra.Smooth R (Localization.Away s) := by
      apply smooth_away_of_isSmoothAt
      intro q _ hq
      exact isSmoothAt_of_smooth_away hts q (fun htq ↦ hq (Ideal.mul_mem_right _ _ htq))
    have hπL2 : ∀ y : Localization.Away s,
        algebraMap R (Localization.Away s) π ^ 2 • y = 0 →
          algebraMap R (Localization.Away s) π • y = 0 := by
      intro y hy
      have := smul_eq_zero_of_flat (R := R) (M := Localization.Away s) hR (y := y)
        (by rw [Algebra.smul_def, map_pow]; exact hy)
      rwa [Algebra.smul_def] at this
    have hunitr₀ : IsUnit (algebraMap _ (Localization.Away s) r₀) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s
      rw [map_mul] at this
      exact isUnit_of_mul_isUnit_right this
    have hxL : algebraMap _ (Localization.Away s) x' = algebraMap R (Localization.Away s) π := by
      rw [← hx', IsScalarTower.algebraMap_apply R
        (MvPolynomial (Fin n ⊕ (Fin c ⊕ Fin n)) D ⧸ K') (Localization.Away s),
        ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_apply, hπϖ]
    have hNker : N ≤ RingHom.ker (algebraMap _ (Localization.Away s)) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      beta_reduce
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hn1 j)
      have hM : x' * Ideal.Quotient.mk K' (relF (D := D) (c := c) f j) ∈ M :=
        Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.subset_span ⟨j, rfl⟩)
      have h0 := hr₀M _ hM
      rw [smul_eq_mul] at h0
      have h1 : algebraMap R (Localization.Away s) π *
          algebraMap _ _ (Ideal.Quotient.mk K' (relF (D := D) (c := c) f j)) = 0 := by
        have := congrArg (algebraMap _ (Localization.Away s)) h0
        rw [map_mul, map_mul, map_zero, hxL] at this
        exact (hunitr₀.mul_right_eq_zero).mp this
      rw [← hw, map_mul, map_pow, hxL] at h1 ⊢
      have h2 : algebraMap R (Localization.Away s) π ^ (2 + 1) •
          algebraMap _ (Localization.Away s) w = 0 := by
        rw [smul_eq_mul]
        linear_combination h1
      have h3 := smul_eq_zero_of_pow_smul_eq_zero (R := Localization.Away s)
        (M := Localization.Away s) (π := algebraMap R _ π) (fun y hy ↦ hπL2 y hy) 2 h2
      rw [smul_eq_mul] at h3
      linear_combination (algebraMap R (Localization.Away s) π) * h3
    have hKK' : K ≤ K' ⊔ Ideal.span (Set.range (relF (D := D) (c := c) f)) := by
      refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
      · rintro _ ⟨(i | j'), rfl⟩
        · exact Ideal.mem_sup_left (Ideal.subset_span ⟨Sum.inl i, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.subset_span ⟨_, rfl⟩)
      · rintro _ ⟨(j | j'), rfl⟩
        · exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_left (Ideal.subset_span ⟨Sum.inr j', rfl⟩)
    have hkill : ∀ y ∈ RingHom.ker p', algebraMap _ (Localization.Away s) y = 0 := by
      intro y hy
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [RingHom.mem_ker, hp', Ideal.Quotient.eq_zero_iff_mem] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hKK' hy)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, ← RingHom.mem_ker]
      apply hNker
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk K') hb
      rw [Ideal.map_span, ← Set.range_comp] at this
      exact this
    have hsmB := smooth_away_of_ker p' hp'surj s hkill
    exact isSmoothAt_of_smooth_away hsmB 𝔮 (fun h𝔮 ↦ hs𝔮 h𝔮)

end Main

end Langlands.CommutativeAlgebra.Popescu.Desing
