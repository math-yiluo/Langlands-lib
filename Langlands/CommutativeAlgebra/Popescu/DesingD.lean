import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.Popescu.DesingChart
import Langlands.CommutativeAlgebra.Popescu.DesingLifting

/-! # Stacks 07CP: lifting a factorization modulo `ϖ²` to an algebra `D` smooth over the chart locus -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.Desing

open MvPolynomial

/-- A chart for the relations `f` (Stacks 07CP): relations `f ∘ e`, variables `u`, an element `a`
and witnesses `a f_ℓ = Σ_j h_{ℓ j} f_{e j} + ϖ² g_ℓ`, chosen trivially on `range e`. -/
structure Chart {R : Type u} [CommRing R] (ϖ : R) {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) R) where
  c : ℕ
  e : Fin c → Fin m
  u : Fin c → Fin n
  a : MvPolynomial (Fin n) R
  h : Fin m → Fin c → MvPolynomial (Fin n) R
  g : Fin m → MvPolynomial (Fin n) R
  e_inj : Function.Injective e
  u_inj : Function.Injective u
  rel : ∀ ℓ, a * f ℓ = ∑ j, h ℓ j * f (e j) + C (ϖ ^ 2) * g ℓ
  h_e : ∀ j₀ j, h (e j₀) j = if j = j₀ then a else 0
  g_e : ∀ j₀, g (e j₀) = 0

section Relations

variable {R : Type u} [CommRing R] (ϖ : R) {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) R)

/-- The relation `f_ℓ(x) − ϖ z_ℓ` of `D`. -/
noncomputable def relE (ℓ : Fin m) : MvPolynomial (Fin n ⊕ Fin m) R :=
  rename Sum.inl (f ℓ) - C ϖ * X (Sum.inr ℓ)

/-- The relation `p_{k, ℓ} = a z_ℓ − Σ_j h_{ℓ j} z_{e j} − ϖ g_ℓ` of `D`. -/
noncomputable def relP (K : Chart ϖ f) (ℓ : Fin m) : MvPolynomial (Fin n ⊕ Fin m) R :=
  rename Sum.inl K.a * X (Sum.inr ℓ) - ∑ j, rename Sum.inl (K.h ℓ j) * X (Sum.inr (K.e j)) -
    C ϖ * rename Sum.inl (K.g ℓ)

variable {ϖ f}

/-- Stacks 07CP, the key identity `ϖ p_{k,ℓ} = −a (f_ℓ − ϖ z_ℓ) + Σ_j h_{ℓ j} (f_{e j} − ϖ z_{e j})`. -/
theorem relP_key (K : Chart ϖ f) (ℓ : Fin m) :
    C ϖ * relP ϖ f K ℓ = -(rename Sum.inl K.a * relE ϖ f ℓ) +
      ∑ j, rename Sum.inl (K.h ℓ j) * relE ϖ f (K.e j) := by
  have h1 := congrArg (rename (R := R) (Sum.inl : Fin n → Fin n ⊕ Fin m)) (K.rel ℓ)
  simp only [map_add, map_mul, map_sum, rename_C] at h1
  simp only [relP, relE, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have h2 : ∑ j, rename Sum.inl (K.h ℓ j) * (C ϖ * X (Sum.inr (K.e j))) =
      ∑ j, C ϖ * (rename Sum.inl (K.h ℓ j) * X (Sum.inr (K.e j))) :=
    Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h2]
  simp only [map_pow] at h1
  linear_combination h1

theorem relP_e (K : Chart ϖ f) (j₀ : Fin K.c) : relP ϖ f K (K.e j₀) = 0 := by
  classical
  simp only [relP, K.h_e, K.g_e, map_zero, mul_zero, sub_zero]
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

end Relations

section Cross

variable {R : Type u} [CommRing R] {ϖ : R} {n m : ℕ} {f : Fin m → MvPolynomial (Fin n) R}

/-- The coefficients `a' h_{ℓ j} − Σ_{j'} h'_{ℓ j'} h_{e' j', j}` comparing two charts. -/
noncomputable def crossCoeff (K K' : Chart ϖ f) (ℓ : Fin m) (j : Fin K.c) : MvPolynomial (Fin n) R :=
  K'.a * K.h ℓ j - ∑ j', K'.h ℓ j' * K.h (K'.e j') j

/-- Stacks 07CP: comparing the relations `a a' f_ℓ` of two charts. -/
theorem crossCoeff_rel (K K' : Chart ϖ f) (ℓ : Fin m) :
    ∑ j, crossCoeff K K' ℓ j * f (K.e j) =
      C (ϖ ^ 2) * (K.a * K'.g ℓ + ∑ j', K'.h ℓ j' * K.g (K'.e j') - K'.a * K.g ℓ) := by
  have h1 := K.rel ℓ
  have h2 := K'.rel ℓ
  have h3 : ∀ j', K.a * f (K'.e j') =
      ∑ j, K.h (K'.e j') j * f (K.e j) + C (ϖ ^ 2) * K.g (K'.e j') := fun j' ↦ K.rel _
  have t1 : ∀ j, crossCoeff K K' ℓ j * f (K.e j) = K'.a * (K.h ℓ j * f (K.e j)) -
      ∑ j', K'.h ℓ j' * (K.h (K'.e j') j * f (K.e j)) := by
    intro j
    simp only [crossCoeff, sub_mul, Finset.sum_mul, mul_assoc]
  have e1 : ∑ j, crossCoeff K K' ℓ j * f (K.e j) =
      K'.a * ∑ j, K.h ℓ j * f (K.e j) - ∑ j', K'.h ℓ j' * ∑ j, K.h (K'.e j') j * f (K.e j) := by
    rw [Finset.sum_congr rfl fun j _ ↦ t1 j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
    simp only [Finset.mul_sum]
  have t2 : ∀ j', K'.h ℓ j' * ∑ j, K.h (K'.e j') j * f (K.e j) =
      K.a * (K'.h ℓ j' * f (K'.e j')) - C (ϖ ^ 2) * (K'.h ℓ j' * K.g (K'.e j')) := by
    intro j'
    rw [show ∑ j, K.h (K'.e j') j * f (K.e j) = K.a * f (K'.e j') - C (ϖ ^ 2) * K.g (K'.e j') by
      rw [h3 j']; ring]
    ring
  have e2 : ∑ j', K'.h ℓ j' * ∑ j, K.h (K'.e j') j * f (K.e j) =
      K.a * ∑ j', K'.h ℓ j' * f (K'.e j') - C (ϖ ^ 2) * ∑ j', K'.h ℓ j' * K.g (K'.e j') := by
    rw [Finset.sum_congr rfl fun j' _ ↦ t2 j', Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [e1, e2, show ∑ j, K.h ℓ j * f (K.e j) = K.a * f ℓ - C (ϖ ^ 2) * K.g ℓ by rw [h1]; ring,
    show ∑ j', K'.h ℓ j' * f (K'.e j') = K'.a * f ℓ - C (ϖ ^ 2) * K'.g ℓ by rw [h2]; ring]
  ring

/-- Stacks 07CP: `a p_{k',ℓ} − a' p_{k,ℓ} + Σ_{j'} h'_{ℓ j'} p_{k, e' j'}` only involves `z_{e j}` and `ϖ`. -/
theorem relP_cross (K K' : Chart ϖ f) (ℓ : Fin m) :
    rename Sum.inl K.a * relP ϖ f K' ℓ - rename Sum.inl K'.a * relP ϖ f K ℓ +
      ∑ j', rename Sum.inl (K'.h ℓ j') * relP ϖ f K (K'.e j') =
    ∑ j, rename Sum.inl (crossCoeff K K' ℓ j) * X (Sum.inr (K.e j)) +
      C ϖ * rename Sum.inl (K'.a * K.g ℓ - K.a * K'.g ℓ - ∑ j', K'.h ℓ j' * K.g (K'.e j')) := by
  have t1 : ∀ j', rename Sum.inl (K'.h ℓ j') * relP ϖ f K (K'.e j') =
      rename Sum.inl K.a * (rename Sum.inl (K'.h ℓ j') * X (Sum.inr (K'.e j'))) -
        ∑ j, rename Sum.inl (K'.h ℓ j') *
          (rename Sum.inl (K.h (K'.e j') j) * X (Sum.inr (K.e j))) -
        C ϖ * (rename Sum.inl (K'.h ℓ j') * rename Sum.inl (K.g (K'.e j'))) := by
    intro j'
    simp only [relP, mul_sub, Finset.mul_sum]
    ring
  have hA : ∑ j', rename Sum.inl (K'.h ℓ j') * relP ϖ f K (K'.e j') =
      rename Sum.inl K.a * ∑ j', rename Sum.inl (K'.h ℓ j') * X (Sum.inr (K'.e j')) -
        ∑ j', ∑ j, rename Sum.inl (K'.h ℓ j') *
          (rename Sum.inl (K.h (K'.e j') j) * X (Sum.inr (K.e j))) -
        C ϖ * ∑ j', rename Sum.inl (K'.h ℓ j') * rename Sum.inl (K.g (K'.e j')) := by
    rw [Finset.sum_congr rfl fun j' _ ↦ t1 j', Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have t2 : ∀ j, rename Sum.inl (crossCoeff K K' ℓ j) * X (Sum.inr (K.e j)) =
      rename Sum.inl K'.a * (rename Sum.inl (K.h ℓ j) * X (Sum.inr (K.e j))) -
        ∑ j', rename Sum.inl (K'.h ℓ j') *
          (rename Sum.inl (K.h (K'.e j') j) * X (Sum.inr (K.e j))) := by
    intro j
    simp only [crossCoeff, map_sub, map_mul, map_sum, sub_mul, Finset.sum_mul, mul_assoc]
  have hB : ∑ j, rename Sum.inl (crossCoeff K K' ℓ j) * X (Sum.inr (K.e j)) =
      rename Sum.inl K'.a * ∑ j, rename Sum.inl (K.h ℓ j) * X (Sum.inr (K.e j)) -
        ∑ j', ∑ j, rename Sum.inl (K'.h ℓ j') *
          (rename Sum.inl (K.h (K'.e j') j) * X (Sum.inr (K.e j))) := by
    rw [Finset.sum_congr rfl fun j _ ↦ t2 j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have hC : rename (Sum.inl : Fin n → Fin n ⊕ Fin m)
      (K'.a * K.g ℓ - K.a * K'.g ℓ - ∑ j', K'.h ℓ j' * K.g (K'.e j')) =
      rename Sum.inl K'.a * rename Sum.inl (K.g ℓ) - rename Sum.inl K.a * rename Sum.inl (K'.g ℓ) -
        ∑ j', rename Sum.inl (K'.h ℓ j') * rename Sum.inl (K.g (K'.e j')) := by
    simp only [map_sub, map_mul, map_sum]
  have hP : ∀ K'' : Chart ϖ f, relP ϖ f K'' ℓ = rename Sum.inl K''.a * X (Sum.inr ℓ) -
      ∑ j, rename Sum.inl (K''.h ℓ j) * X (Sum.inr (K''.e j)) -
        C ϖ * rename Sum.inl (K''.g ℓ) := fun _ ↦ rfl
  rw [hA, hB, hC, hP K, hP K']
  ring

/-- The derivative argument of Stacks 07CP: from `Σ_j c_j f_{e j} ∈ (ϖ²)`, the Jacobian minor of the
chart kills each `c_j` modulo `(f) + (ϖ²)`. -/
theorem det_mul_mem_of_sum {c : ℕ} (e : Fin c → Fin m) (u : Fin c → Fin n)
    (cc : Fin c → MvPolynomial (Fin n) R) (G : MvPolynomial (Fin n) R)
    (hcc : ∑ j, cc j * f (e j) = C (ϖ ^ 2) * G) (j : Fin c) :
    Matrix.det (Matrix.of fun j l : Fin c ↦ pderiv (u l) (f (e j))) * cc j ∈
      Ideal.span (Set.range f) ⊔ Ideal.span {C (ϖ ^ 2)} := by
  classical
  set J := Ideal.span (Set.range f) ⊔ Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin n) R)}
  have hfJ : ∀ j, f j ∈ J := fun j ↦ Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
  have hv : ∀ l, ∑ j, cc j * pderiv (u l) (f (e j)) ∈ J := by
    intro l
    have h1 := congrArg (pderiv (u l)) hcc
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero] at h1
    have h2 : ∑ j, cc j * pderiv (u l) (f (e j)) =
        C (ϖ ^ 2) * pderiv (u l) G - ∑ j, f (e j) * pderiv (u l) (cc j) := by
      rw [← h1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [h2]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))) ?_
    exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_right _ _ (hfJ _)
  let M : Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) R) :=
    Matrix.of fun j l : Fin c ↦ pderiv (u l) (f (e j))
  let Mq := (Ideal.Quotient.mk J).mapMatrix M
  let cq : Fin c → MvPolynomial (Fin n) R ⧸ J := fun j ↦ Ideal.Quotient.mk J (cc j)
  have hvq : Matrix.vecMul cq Mq = 0 := by
    ext l
    simp only [Matrix.vecMul, dotProduct, Mq, M, cq, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, ← map_mul, ← map_sum, Pi.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv l)
  have hdet : Matrix.vecMul cq (Mq * Mq.adjugate) = 0 := by
    rw [← Matrix.vecMul_vecMul, hvq, Matrix.zero_vecMul]
  rw [Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one] at hdet
  have h3 := congrFun hdet j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, cq] at h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul,
    RingHom.map_det (S := MvPolynomial (Fin n) R ⧸ J) (Ideal.Quotient.mk J) M]
  exact h3

end Cross

section ChartJacobian

variable {R : Type u} [CommRing R] {ϖ : R} {n m : ℕ} {f : Fin m → MvPolynomial (Fin n) R}

open Classical in
/-- The Jacobian of the chart `D_k = R[x, z] ⧸ (f_{e j} − ϖ z_{e j}, p_{k,ℓ} (ℓ ∉ range e))` along the
variables `x_{u j}` and `z_ℓ` (`ℓ ∉ range e`): it is `δ · a^#`. -/
theorem det_chart (K : Chart ϖ f) :
    Matrix.det (Matrix.of fun i j : Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} ↦
      pderiv ((Sum.elim (fun j ↦ Sum.inl (K.u j)) (fun ℓ ↦ Sum.inr ℓ.1) :
          Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → Fin n ⊕ Fin m) i)
        ((Sum.elim (fun j ↦ relE ϖ f (K.e j)) (fun ℓ ↦ relP ϖ f K ℓ.1) :
          Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → MvPolynomial (Fin n ⊕ Fin m) R) j)) =
      rename Sum.inl (Matrix.det (Matrix.of fun j l : Fin K.c ↦ pderiv (K.u l) (f (K.e j)))) *
        rename Sum.inl K.a ^ Fintype.card {ℓ // ℓ ∉ Set.range K.e} := by
  let A : Matrix (Fin K.c) (Fin K.c) (MvPolynomial (Fin n ⊕ Fin m) R) :=
    Matrix.of fun j1 j2 ↦ rename Sum.inl (pderiv (K.u j1) (f (K.e j2)))
  let B : Matrix (Fin K.c) {ℓ // ℓ ∉ Set.range K.e} (MvPolynomial (Fin n ⊕ Fin m) R) :=
    Matrix.of fun j1 ℓ2 ↦ pderiv (Sum.inl (K.u j1)) (relP ϖ f K ℓ2.1)
  have hM : (Matrix.of fun i j : Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} ↦
      pderiv ((Sum.elim (fun j ↦ Sum.inl (K.u j)) (fun ℓ ↦ Sum.inr ℓ.1) :
          Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → Fin n ⊕ Fin m) i)
        ((Sum.elim (fun j ↦ relE ϖ f (K.e j)) (fun ℓ ↦ relP ϖ f K ℓ.1) :
          Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → MvPolynomial (Fin n ⊕ Fin m) R) j)) =
      Matrix.fromBlocks A B 0 ((rename Sum.inl K.a : MvPolynomial (Fin n ⊕ Fin m) R) • (1 : Matrix {ℓ // ℓ ∉ Set.range K.e}
        {ℓ // ℓ ∉ Set.range K.e} (MvPolynomial (Fin n ⊕ Fin m) R))) := by
    refine Matrix.ext fun i j ↦ ?_
    rcases i with j1 | ℓ1 <;> rcases j with j2 | ℓ2
    · simp only [Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, A, relE, map_sub,
        Derivation.leibniz, pderiv_C, pderiv_X, smul_eq_mul, Pi.single_apply, reduceCtorEq,
        ite_false, mul_zero, zero_add, sub_zero]
      exact pderiv_rename Sum.inl_injective _ _
    · rfl
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, relE, map_sub, Derivation.leibniz, pderiv_C, pderiv_X, smul_eq_mul,
        Pi.single_apply, Sum.inr.injEq, mul_zero, add_zero]
      rw [pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inl_ne_inr)]
      have : K.e j2 ≠ ℓ1.1 := fun h ↦ ℓ1.2 ⟨j2, h⟩
      simp [this]
    · simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, relP, map_sub,
        map_sum, Derivation.leibniz, pderiv_C, pderiv_X, smul_eq_mul, Pi.single_apply,
        Sum.inr.injEq, mul_zero, add_zero, Matrix.smul_apply, Matrix.one_apply]
      rw [pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inl_ne_inr),
        pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inl_ne_inr)]
      have h0 : ∀ j, K.e j ≠ ℓ1.1 := fun j h ↦ ℓ1.2 ⟨j, h⟩
      have hz := pderiv_rename_eq_zero (D := R) (Sum.inl : Fin n → Fin n ⊕ Fin m) (Sum.inr ℓ1.1)
        (fun _ ↦ Sum.inl_ne_inr)
      simp only [h0, ite_false, mul_zero, add_zero, sub_zero, hz]
      by_cases hl : ℓ1 = ℓ2
      · subst hl
        simp
      · have hl' : ℓ2.1 ≠ ℓ1.1 := fun h ↦ hl (Subtype.ext h.symm)
        simp [hl, hl']
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one, mul_one, AlgHom.map_det,
    ← Matrix.det_transpose]
  rfl

end ChartJacobian

section Kill

variable {R : Type u} [CommRing R] {ϖ : R} {n m : ℕ} {f : Fin m → MvPolynomial (Fin n) R}

/-- Stacks 07CP, the comparison of charts: a ring map out of `R[x, z]` killing the relations
`f_ℓ − ϖ z_ℓ` and the `p_{k, ℓ}` of one chart `K`, inverting `a_K δ_K`, and with
`Ann(ϖ) = Ann(ϖ²)` in the target, kills the `p_{k', ℓ}` of every other chart. -/
theorem relP_eq_zero_of_chart {L : Type*} [CommRing L] (φL : MvPolynomial (Fin n ⊕ Fin m) R →+* L)
    (K : Chart ϖ f) (hE : ∀ ℓ, φL (relE ϖ f ℓ) = 0) (hPK : ∀ ℓ, φL (relP ϖ f K ℓ) = 0)
    (hunit : IsUnit (φL (rename Sum.inl
      (K.a * Matrix.det (Matrix.of fun j l : Fin K.c ↦ pderiv (K.u l) (f (K.e j)))))))
    (hAnn : ∀ y : L, φL (C ϖ) ^ 2 * y = 0 → φL (C ϖ) * y = 0) (K' : Chart ϖ f) (ℓ : Fin m) :
    φL (relP ϖ f K' ℓ) = 0 := by
  classical
  set w := φL (C ϖ) with hw
  set δ := Matrix.det (Matrix.of fun j l : Fin K.c ↦ pderiv (K.u l) (f (K.e j))) with hδ
  -- (1) `ϖ p' ↦ 0`
  have h1 : w * φL (relP ϖ f K' ℓ) = 0 := by
    rw [hw, ← map_mul, relP_key, map_add, map_neg, map_mul, hE, mul_zero, neg_zero, zero_add,
      map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [map_mul, hE, mul_zero]
  -- (2) everything in `(f) + (ϖ²)` maps into `(w)`
  have h2 : Ideal.span (Set.range f) ⊔ Ideal.span {C (ϖ ^ 2)} ≤
      (Ideal.span {w}).comap (φL.comp (rename (R := R) (Sum.inl : Fin n → Fin n ⊕ Fin m)).toRingHom) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : φL (rename Sum.inl (f j)) = w * φL (X (Sum.inr j)) := by
        have := hE j
        rw [relE, map_sub, sub_eq_zero, map_mul] at this
        exact this
      show φL (rename Sum.inl (f j)) ∈ Ideal.span {w}
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show φL (rename Sum.inl (C (ϖ ^ 2))) ∈ Ideal.span {w}
      rw [rename_C, map_pow, map_pow, pow_two]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  -- (3) the cross coefficients times `δ` map into `(w)`
  have h3 : ∀ j, φL (rename Sum.inl δ) * φL (rename Sum.inl (crossCoeff K K' ℓ j)) ∈
      Ideal.span {w} := by
    intro j
    rw [← map_mul, ← map_mul]
    exact h2 (det_mul_mem_of_sum K.e K.u _ _ (crossCoeff_rel K K' ℓ) j)
  -- (4) the comparison identity
  have h4 := congrArg φL (relP_cross K K' ℓ)
  simp only [map_add, map_sub, map_mul, map_sum, hPK, mul_zero, sub_zero, Finset.sum_const_zero,
    add_zero] at h4
  have h5 : φL (rename Sum.inl δ) * φL (rename Sum.inl K.a) * φL (relP ϖ f K' ℓ) ∈
      Ideal.span {w} := by
    rw [mul_assoc, h4, mul_add, Finset.mul_sum]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun j _ ↦ ?_) ?_
    · rw [← mul_assoc]
      exact Ideal.mul_mem_right _ _ (h3 j)
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  have h6 : φL (relP ϖ f K' ℓ) ∈ Ideal.span {w} := by
    have hv' : v * (φL (rename Sum.inl δ) * φL (rename Sum.inl K.a)) = 1 := by
      rw [← hv, map_mul, map_mul, mul_comm (φL (rename Sum.inl K.a))]
    have : φL (relP ϖ f K' ℓ) =
        v * (φL (rename Sum.inl δ) * φL (rename Sum.inl K.a) * φL (relP ϖ f K' ℓ)) := by
      calc φL (relP ϖ f K' ℓ) =
          (v * (φL (rename Sum.inl δ) * φL (rename Sum.inl K.a))) * φL (relP ϖ f K' ℓ) := by
            rw [hv', one_mul]
        _ = _ := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ h5
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h6
  rw [← hy] at h1 ⊢
  have h7 : w ^ 2 * y = 0 := by rw [← h1]; ring
  rw [mul_comm]
  exact hAnn y h7

end Kill

section Smooth

variable {R : Type u} [CommRing R] {ϖ : R} {n m : ℕ} {f : Fin m → MvPolynomial (Fin n) R}

/-- The ideal of the algebra `D` of Stacks 07CP built from finitely many charts. -/
noncomputable def idealD {r : ℕ} (charts : Fin r → Chart ϖ f) :
    Ideal (MvPolynomial (Fin n ⊕ Fin m) R) :=
  Ideal.span (Set.range (relE ϖ f)) ⊔
    Ideal.span (Set.range fun kℓ : Fin r × Fin m ↦ relP ϖ f (charts kℓ.1) kℓ.2)

theorem fg_idealD {r : ℕ} (charts : Fin r → Chart ϖ f) : (idealD charts).FG :=
  (Submodule.fg_span (Set.finite_range _)).sup (Submodule.fg_span (Set.finite_range _))

/-- Kernel of a quotient map `P ⧸ I → P ⧸ (I ⊔ J)`: it is the image of `J`. -/
theorem factor_ker_mem {P : Type*} [CommRing P] {I J : Ideal P} (y : P ⧸ I)
    (hy : y ∈ RingHom.ker (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))) :
    ∃ b ∈ J, y = Ideal.Quotient.mk I b := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  refine ⟨b, hb, ?_⟩
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]

/-- Stacks 07CP (b): `D` is smooth over `R` away from `ϖ`. -/
theorem isSmoothAt_D_of_notMem {r : ℕ} (charts : Fin r → Chart ϖ f)
    (q : Ideal (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts)) [q.IsPrime]
    (hq : Ideal.Quotient.mk _ (C ϖ) ∉ q) : Algebra.IsSmoothAt R q := by
  classical
  let I₀ := Ideal.span (Set.range (relE ϖ f))
  let jac := Matrix.det fun i j : Fin m ↦ pderiv (Sum.inr i : Fin n ⊕ Fin m) (relE ϖ f j)
  have hjac : jac = (-C ϖ) ^ m := by
    have : (Matrix.of fun i j : Fin m ↦ pderiv (Sum.inr i : Fin n ⊕ Fin m) (relE ϖ f j)) =
        (-C ϖ : MvPolynomial (Fin n ⊕ Fin m) R) • (1 : Matrix (Fin m) (Fin m) _) := by
      refine Matrix.ext fun i j ↦ ?_
      simp only [Matrix.of_apply, relE, map_sub, Derivation.leibniz, pderiv_C, pderiv_X,
        smul_eq_mul, Pi.single_apply, Sum.inr.injEq, mul_zero, add_zero, Matrix.smul_apply,
        Matrix.one_apply]
      rw [pderiv_rename_eq_zero _ _ (fun _ ↦ Sum.inl_ne_inr)]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    show Matrix.det (Matrix.of fun i j : Fin m ↦ pderiv (Sum.inr i : Fin n ⊕ Fin m) (relE ϖ f j)) = _
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hstd := isStandardSmooth_away_det_mul (relE ϖ f) (Sum.inr : Fin m → Fin n ⊕ Fin m)
    Sum.inr_injective (Ideal.Quotient.mk I₀ (C ϖ))
  set s₀ := Ideal.Quotient.mk I₀ jac * Ideal.Quotient.mk I₀ (C ϖ) with hs₀
  let p : (MvPolynomial (Fin n ⊕ Fin m) R ⧸ I₀) →ₐ[R]
      MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts := Ideal.Quotient.factorₐ R le_sup_left
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I₀ x, rfl⟩
  have hunit : IsUnit (algebraMap _ (Localization.Away s₀) (Ideal.Quotient.mk I₀ (C ϖ))) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s₀) s₀
    rw [hs₀, map_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have hkill : ∀ y ∈ RingHom.ker p, algebraMap _ (Localization.Away s₀) y = 0 := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := factor_ker_mem y hy
    have hle : Ideal.span (Set.range fun kℓ : Fin r × Fin m ↦ relP ϖ f (charts kℓ.1) kℓ.2) ≤
        RingHom.ker ((algebraMap _ (Localization.Away s₀)).comp (Ideal.Quotient.mk I₀)) := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨k, ℓ⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply]
      have h1 : Ideal.Quotient.mk I₀ (C ϖ * relP ϖ f (charts k) ℓ) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, relP_key]
        refine Ideal.add_mem _ (neg_mem (Ideal.mul_mem_left _ _
          (Ideal.subset_span ⟨ℓ, rfl⟩))) (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _
          (Ideal.subset_span ⟨_, rfl⟩))
      have h2 := congrArg (algebraMap _ (Localization.Away s₀)) h1
      rw [map_mul, map_mul, map_zero] at h2
      exact (hunit.mul_right_eq_zero).mp h2
    exact hle hb
  have hsm := smooth_away_of_ker p hpsurj s₀ hkill
  have hFP : Algebra.FinitePresentation R (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) :=
    Algebra.FinitePresentation.quotient (fg_idealD charts)
  refine isSmoothAt_of_smooth_away hsm q ?_
  rw [hs₀, map_mul, hjac]
  show Ideal.Quotient.mk _ ((-C ϖ) ^ m) * Ideal.Quotient.mk _ (C ϖ) ∉ q
  rw [map_pow, map_neg]
  refine (inferInstance : q.IsPrime).mul_notMem ?_ hq
  intro hmem
  exact hq (by simpa using (inferInstance : q.IsPrime).mem_of_pow_mem _ hmem)

open Classical in
/-- Stacks 07CP (c): `D` is smooth over `R` on the chart `D(a_k δ_k)` (for `Ann(ϖ) = Ann(ϖ²)`). -/
theorem isSmoothAt_D_of_chart (hR : ∀ x : R, ϖ ^ 2 * x = 0 → ϖ * x = 0) {r : ℕ}
    (charts : Fin r → Chart ϖ f) (k : Fin r)
    (q : Ideal (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts)) [q.IsPrime]
    (hq : Ideal.Quotient.mk _ (rename Sum.inl ((charts k).a * Matrix.det
      (Matrix.of fun j l : Fin (charts k).c ↦ pderiv ((charts k).u l) (f ((charts k).e j))))) ∉ q) :
    Algebra.IsSmoothAt R q := by
  set K := charts k with hK
  set δ := Matrix.det (Matrix.of fun j l : Fin K.c ↦ pderiv (K.u l) (f (K.e j))) with hδ
  let vK : Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → MvPolynomial (Fin n ⊕ Fin m) R :=
    Sum.elim (fun j ↦ relE ϖ f (K.e j)) (fun ℓ ↦ relP ϖ f K ℓ.1)
  let μ : Fin K.c ⊕ {ℓ // ℓ ∉ Set.range K.e} → Fin n ⊕ Fin m :=
    Sum.elim (fun j ↦ Sum.inl (K.u j)) (fun ℓ ↦ Sum.inr ℓ.1)
  have hμ : Function.Injective μ := Function.Injective.sumElim
    (Sum.inl_injective.comp K.u_inj) (Sum.inr_injective.comp Subtype.val_injective)
    (fun _ _ ↦ Sum.inl_ne_inr)
  let Ik := Ideal.span (Set.range vK)
  have hstd := isStandardSmooth_away_det_mul vK μ hμ (Ideal.Quotient.mk Ik (rename Sum.inl K.a))
  set jac := Matrix.det fun i j ↦ pderiv (μ i) (vK j) with hjac_def
  have hjac : jac = rename Sum.inl δ * rename Sum.inl K.a ^ Fintype.card {ℓ // ℓ ∉ Set.range K.e} :=
    det_chart K
  set s := Ideal.Quotient.mk Ik jac * Ideal.Quotient.mk Ik (rename Sum.inl K.a) with hs
  -- membership of the chart relations
  have hPK_mem : ∀ ℓ, relP ϖ f K ℓ ∈ Ik := by
    intro ℓ
    by_cases hℓ : ℓ ∈ Set.range K.e
    · obtain ⟨j, rfl⟩ := hℓ
      rw [relP_e]
      exact Ik.zero_mem
    · exact Ideal.subset_span ⟨Sum.inr ⟨ℓ, hℓ⟩, rfl⟩
  have hIk : Ik ≤ idealD charts := by
    rw [Ideal.span_le]
    rintro _ ⟨(j | ℓ), rfl⟩
    · exact Ideal.mem_sup_left (Ideal.subset_span ⟨_, rfl⟩)
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨(k, ℓ.1), rfl⟩)
  -- the localization `L`
  let φL : MvPolynomial (Fin n ⊕ Fin m) R →+* Localization.Away s :=
    (algebraMap _ (Localization.Away s)).comp (Ideal.Quotient.mk Ik)
  have hsu : IsUnit (algebraMap _ (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit s
  have hsu' : IsUnit (φL (rename Sum.inl δ) * φL (rename Sum.inl K.a) ^
      Fintype.card {ℓ // ℓ ∉ Set.range K.e} * φL (rename Sum.inl K.a)) := by
    have : algebraMap _ (Localization.Away s) s = φL (rename Sum.inl δ) *
        φL (rename Sum.inl K.a) ^ Fintype.card {ℓ // ℓ ∉ Set.range K.e} *
          φL (rename Sum.inl K.a) := by
      show algebraMap _ (Localization.Away s)
        (Ideal.Quotient.mk Ik jac * Ideal.Quotient.mk Ik (rename Sum.inl K.a)) = _
      rw [map_mul, hjac]
      simp only [φL, RingHom.comp_apply, map_mul, map_pow]
    rw [← this]
    exact hsu
  have hau : IsUnit (φL (rename Sum.inl K.a)) := isUnit_of_mul_isUnit_right hsu'
  have hδu : IsUnit (φL (rename Sum.inl δ)) :=
    isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hsu')
  have hPK : ∀ ℓ, φL (relP ϖ f K ℓ) = 0 := fun ℓ ↦ by
    simp only [φL, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (hPK_mem ℓ), map_zero]
  have hE : ∀ ℓ, φL (relE ϖ f ℓ) = 0 := by
    intro ℓ
    have h1 : rename Sum.inl K.a * relE ϖ f ℓ ∈ Ik := by
      have := relP_key K ℓ
      have e : rename Sum.inl K.a * relE ϖ f ℓ =
          ∑ j, rename Sum.inl (K.h ℓ j) * relE ϖ f (K.e j) - C ϖ * relP ϖ f K ℓ := by
        rw [this]
        ring
      rw [e]
      refine Ideal.sub_mem _ (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨Sum.inl j, rfl⟩)) (Ideal.mul_mem_left _ _ (hPK_mem ℓ))
    have h2 : φL (rename Sum.inl K.a * relE ϖ f ℓ) = 0 := by
      simp only [φL, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr h1, map_zero]
    rw [map_mul] at h2
    exact (hau.mul_right_eq_zero).mp h2
  have hunit : IsUnit (φL (rename Sum.inl (K.a * δ))) := by
    rw [map_mul, map_mul]
    exact hau.mul hδu
  have hflat : Module.Flat R (Localization.Away s) := inferInstance
  have hAnn : ∀ y : Localization.Away s, φL (C ϖ) ^ 2 * y = 0 → φL (C ϖ) * y = 0 := by
    intro y hy
    have hφC : φL (C ϖ) = algebraMap R (Localization.Away s) ϖ := by
      simp only [φL, RingHom.comp_apply]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
        ← IsScalarTower.algebraMap_apply]
    rw [hφC] at hy ⊢
    have := smul_eq_zero_of_flat (R := R) (M := Localization.Away s) hR (y := y)
      (by rw [Algebra.smul_def, map_pow]; exact hy)
    rwa [Algebra.smul_def] at this
  have hkillP : ∀ (k' : Fin r) ℓ, φL (relP ϖ f (charts k') ℓ) = 0 :=
    fun k' ℓ ↦ relP_eq_zero_of_chart φL K hE hPK hunit hAnn (charts k') ℓ
  -- the comparison map `D_k → D`
  let p : (MvPolynomial (Fin n ⊕ Fin m) R ⧸ Ik) →ₐ[R]
      MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts := Ideal.Quotient.factorₐ R hIk
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk Ik x, rfl⟩
  have hkill : ∀ y ∈ RingHom.ker p, algebraMap _ (Localization.Away s) y = 0 := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker] at hy
    change Ideal.Quotient.mk (idealD charts) x = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hy
    have hle : idealD charts ≤ RingHom.ker φL := by
      refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
      · rintro _ ⟨ℓ, rfl⟩
        exact hE ℓ
      · rintro _ ⟨⟨k', ℓ⟩, rfl⟩
        exact hkillP k' ℓ
    exact hle hy
  have hsm := smooth_away_of_ker p hpsurj s hkill
  have hFP : Algebra.FinitePresentation R (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) :=
    Algebra.FinitePresentation.quotient (fg_idealD charts)
  refine isSmoothAt_of_smooth_away hsm q ?_
  have hps : p s = Ideal.Quotient.mk (idealD charts) (rename Sum.inl δ) *
      Ideal.Quotient.mk (idealD charts) (rename Sum.inl K.a) ^
        Fintype.card {ℓ // ℓ ∉ Set.range K.e} *
      Ideal.Quotient.mk (idealD charts) (rename Sum.inl K.a) := by
    rw [hs, map_mul, hjac]
    show Ideal.Quotient.mk (idealD charts) _ * Ideal.Quotient.mk (idealD charts) _ = _
    rw [map_mul, map_pow]
  rw [map_mul, map_mul] at hq
  have ha : Ideal.Quotient.mk (idealD charts) (rename Sum.inl K.a) ∉ q :=
    fun h ↦ hq (Ideal.mul_mem_right _ _ h)
  have hd : Ideal.Quotient.mk (idealD charts) (rename Sum.inl δ) ∉ q :=
    fun h ↦ hq (Ideal.mul_mem_left _ _ h)
  rw [hps]
  refine (inferInstance : q.IsPrime).mul_notMem ((inferInstance : q.IsPrime).mul_notMem hd ?_) ha
  exact fun h ↦ ha ((inferInstance : q.IsPrime).mem_of_pow_mem _ h)

end Smooth

section Charts

/-- Lifting a chart relation from `R ⧸ (ϖ²)` to `R`, with the witnesses chosen trivially on
`range e`. -/
theorem exists_lift_rel {R : Type u} [CommRing R] (ϖ : R) {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) R) {c : ℕ} (e : Fin c → Fin m) (he : Function.Injective e)
    (ā : MvPolynomial (Fin n) (R ⧸ Ideal.span {ϖ ^ 2}))
    (hā : ∀ ℓ, ā * MvPolynomial.map (Ideal.Quotient.mk _) (f ℓ) ∈ Ideal.span (Set.range
      fun j ↦ MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) (f (e j)))) :
    ∃ (a : MvPolynomial (Fin n) R) (h : Fin m → Fin c → MvPolynomial (Fin n) R)
      (g : Fin m → MvPolynomial (Fin n) R),
      MvPolynomial.map (Ideal.Quotient.mk _) a = ā ∧
      (∀ ℓ, a * f ℓ = ∑ j, h ℓ j * f (e j) + C (ϖ ^ 2) * g ℓ) ∧
      (∀ j₀ j, h (e j₀) j = if j = j₀ then a else 0) ∧ (∀ j₀, g (e j₀) = 0) := by
  classical
  have hsurj : Function.Surjective
      (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a, rfl⟩ := hsurj ā
  have hrel0 : ∀ ℓ, ∃ (h : Fin c → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin n) R),
      a * f ℓ = ∑ j, h j * f (e j) + C (ϖ ^ 2) * g := by
    intro ℓ
    obtain ⟨hb, hhb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hā ℓ)
    choose h₀ hh₀ using fun j ↦ hsurj (hb j)
    have hker : a * f ℓ - ∑ j, h₀ j * f (e j) ∈
        RingHom.ker (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_sum, ← hhb]
      simp only [map_mul, hh₀, smul_eq_mul, sub_self]
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hker
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hker
    refine ⟨h₀, g, ?_⟩
    rw [mul_comm g] at hg
    linear_combination -hg
  choose h₀ g₀ hhg using hrel0
  refine ⟨a, fun ℓ j ↦ if ℓ ∈ Set.range e then (if e j = ℓ then a else 0) else h₀ ℓ j,
    fun ℓ ↦ if ℓ ∈ Set.range e then 0 else g₀ ℓ, rfl, fun ℓ ↦ ?_, fun j₀ j ↦ ?_, fun j₀ ↦ ?_⟩
  · by_cases hℓ : ℓ ∈ Set.range e
    · obtain ⟨j₀, rfl⟩ := hℓ
      simp only [Set.mem_range_self, ite_true, mul_zero, add_zero, ite_mul, zero_mul]
      rw [Finset.sum_eq_single j₀]
      · simp
      · intro j _ hj
        simp [he.ne hj]
      · simp
    · simp only [hℓ, ite_false]
      exact hhg ℓ
  · simp only [Set.mem_range_self, ite_true, he.eq_iff]
  · simp only [Set.mem_range_self, ite_true]

/-- Stacks 07CP, the finite chart cover: charts `(e_i, u_i, a_i)` of a presentation of a finitely
presented algebra over a Noetherian ring whose loci `D(a_i δ_i)` cover the smooth locus, so that the
singular ideal lies in the radical of the ideal generated by the `a_i δ_i`. -/
theorem exists_chart_family {k : Type u} [CommRing k] [IsNoetherianRing k] {C : Type u}
    [CommRing C] [Algebra k C] [Algebra.FinitePresentation k C] {n m : ℕ}
    (φ : MvPolynomial (Fin n) k →ₐ[k] C) (hφ : Function.Surjective φ)
    (f : Fin m → MvPolynomial (Fin n) k) (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ (r : ℕ) (c : Fin r → ℕ) (e : ∀ i, Fin (c i) → Fin m) (u : ∀ i, Fin (c i) → Fin n)
      (a : Fin r → MvPolynomial (Fin n) k),
      (∀ i, Function.Injective (e i)) ∧ (∀ i, Function.Injective (u i)) ∧
      (∀ i ℓ, a i * f ℓ ∈ Ideal.span (Set.range (f ∘ e i))) ∧
      ∀ y ∈ singularIdeal k C, ∃ N : ℕ, y ^ N ∈ Ideal.span (Set.range fun i ↦
        φ (a i * Matrix.det (Matrix.of fun j l : Fin (c i) ↦ pderiv (u i l) (f (e i j))))) := by
  classical
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hloc : ∀ q : Algebra.smoothLocus k C, ∃ (c : ℕ) (e : Fin c → Fin m) (u : Fin c → Fin n)
      (a : MvPolynomial (Fin n) k), Function.Injective e ∧ Function.Injective u ∧
      φ (a * Matrix.det (Matrix.of fun j l : Fin c ↦ pderiv (u l) (f (e j)))) ∉ q.1.asIdeal ∧
      ∀ ℓ, a * f ℓ ∈ Ideal.span (Set.range (f ∘ e)) :=
    fun q ↦ exists_chart φ hφ f hker q.1.asIdeal q.2
  choose c e u a he hu hq hrel using hloc
  let U : Algebra.smoothLocus k C → Set (PrimeSpectrum C) := fun q ↦ PrimeSpectrum.basicOpen
    (φ (a q * Matrix.det (Matrix.of fun j l : Fin (c q) ↦ pderiv (u q l) (f (e q j)))))
  have hcover : Algebra.smoothLocus k C ⊆ ⋃ q, U q :=
    fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hq ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact (Algebra.smoothLocus k C)).elim_finite_subcover U
    (fun q ↦ PrimeSpectrum.isOpen_basicOpen) hcover
  let eqv := t.equivFin
  refine ⟨t.card, fun i ↦ c (eqv.symm i).1, fun i ↦ e (eqv.symm i).1, fun i ↦ u (eqv.symm i).1,
    fun i ↦ a (eqv.symm i).1, fun i ↦ he _, fun i ↦ hu _, fun i ℓ ↦ hrel _ ℓ, ?_⟩
  intro y hy
  show y ∈ (Ideal.span _).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hJP, hP⟩
  by_contra hyP
  have hsm : (⟨P, hP⟩ : PrimeSpectrum C) ∈ Algebra.smoothLocus k C := by
    by_contra hns
    exact hyP ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hy ⟨P, hP⟩ hns)
  obtain ⟨q, hqt, hPq⟩ := Set.mem_iUnion₂.mp (ht hsm)
  apply hPq
  refine hJP (Ideal.subset_span ⟨eqv ⟨q, hqt⟩, ?_⟩)
  have key : ∀ q' : Algebra.smoothLocus k C, q' = q →
      φ (a q' * Matrix.det (Matrix.of fun j l : Fin (c q') ↦ pderiv (u q' l) (f (e q' j)))) =
        φ (a q * Matrix.det (Matrix.of fun j l : Fin (c q) ↦ pderiv (u q l) (f (e q j)))) := by
    rintro q' rfl
    rfl
  exact key _ (by simp)

end Charts

section Main

/-- Stacks 07CP in the form used for 07F0. -/
theorem exists_lift_D {R : Type u} [CommRing R] [IsNoetherianRing R] (ϖ ε : R) (hε : ε = ϖ ^ 2)
    (hR : ∀ x : R, ϖ ^ 2 * x = 0 → ϖ * x = 0)
    {Λ : Type u} [CommRing Λ] [Algebra R Λ]
    (hΛ : ∀ x : Λ, algebraMap R Λ ϖ ^ 2 * x = 0 → algebraMap R Λ ϖ * x = 0)
    {Cb : Type u} [CommRing Cb] [Algebra (R ⧸ Ideal.span {ε}) Cb] [Algebra R Cb]
    [IsScalarTower R (R ⧸ Ideal.span {ε}) Cb] [Algebra.FinitePresentation (R ⧸ Ideal.span {ε}) Cb]
    (v : Cb →ₐ[R] Λ ⧸ (Ideal.span {ε}).map (algebraMap R Λ)) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Algebra.FinitePresentation R D ∧
      ∃ (ψ : D →ₐ[R] Λ) (τ : Cb →ₐ[R] D ⧸ Ideal.span {algebraMap R D ϖ}),
        (∀ (c : Cb) (d : D) (l : Λ), τ c = Ideal.Quotient.mk _ d → v c = Ideal.Quotient.mk _ l →
          ∃ z, l - ψ d = algebraMap R Λ ϖ * z) ∧
        (∀ (q : Ideal D) [q.IsPrime], algebraMap R D ϖ ∉ q → Algebra.IsSmoothAt R q) ∧
        ∀ y ∈ singularIdeal (R ⧸ Ideal.span {ε}) Cb, ∀ l : Λ, v y = Ideal.Quotient.mk _ l →
          ∀ (𝔭 : Ideal Λ) [𝔭.IsPrime], algebraMap R Λ ϖ ∈ 𝔭 → l ∉ 𝔭 →
            Algebra.IsSmoothAt R (𝔭.comap ψ) := by
  classical
  subst hε
  -- a presentation of `C` over `R ⧸ (ϖ²)` and lifts of its relations
  obtain ⟨n, φ, hφ, hfg⟩ := Algebra.FinitePresentation.out (R := R ⧸ Ideal.span {ϖ ^ 2}) (A := Cb)
  obtain ⟨m, fb, hfb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hker : RingHom.ker φ = Ideal.span (Set.range fb) := hfb.symm
  have hsurj : Function.Surjective
      (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose f hf using fun j ↦ hsurj (fb j)
  -- the charts
  obtain ⟨r, cc, ee, uu, aa, hee, huu, hrel, hrad⟩ := exists_chart_family φ hφ fb hker
  have hlift : ∀ i, ∃ (a : MvPolynomial (Fin n) R) (h : Fin m → Fin (cc i) → MvPolynomial (Fin n) R)
      (g : Fin m → MvPolynomial (Fin n) R),
      MvPolynomial.map (Ideal.Quotient.mk _) a = aa i ∧
      (∀ ℓ, a * f ℓ = ∑ j, h ℓ j * f (ee i j) + C (ϖ ^ 2) * g ℓ) ∧
      (∀ j₀ j, h (ee i j₀) j = if j = j₀ then a else 0) ∧ (∀ j₀, g (ee i j₀) = 0) := by
    intro i
    refine exists_lift_rel ϖ f (ee i) (hee i) (aa i) fun ℓ ↦ ?_
    have h2 : (fun j ↦ MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) (f (ee i j))) =
        fb ∘ ee i := funext fun j ↦ hf _
    rw [hf ℓ, h2]
    exact hrel i ℓ
  choose A H G hA hrelR hH hG using hlift
  let charts : Fin r → Chart ϖ f := fun i ↦
    { c := cc i, e := ee i, u := uu i, a := A i, h := H i, g := G i, e_inj := hee i,
      u_inj := huu i, rel := hrelR i, h_e := hH i, g_e := hG i }
  -- the map `R[x] → C`
  let ψC : MvPolynomial (Fin n) R →ₐ[R] Cb := aeval fun i ↦ φ (X i)
  have hψC : ∀ p, ψC p = φ (MvPolynomial.map (Ideal.Quotient.mk _) p) := by
    intro p
    have : (ψC : MvPolynomial (Fin n) R →+* Cb) =
        (φ : MvPolynomial (Fin n) (R ⧸ Ideal.span {ϖ ^ 2}) →+* Cb).comp
          (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      apply MvPolynomial.ringHom_ext
      · intro x
        simp only [RingHom.coe_coe, RingHom.comp_apply, MvPolynomial.map_C, ψC, aeval_C]
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Ideal.Quotient.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply]
      · intro i
        simp [ψC]
    exact RingHom.congr_fun this p
  have hψCsurj : Function.Surjective ψC := by
    intro c
    obtain ⟨p, rfl⟩ := hφ c
    obtain ⟨p', rfl⟩ := hsurj p
    exact ⟨p', hψC p'⟩
  have hfb' : ∀ j, ψC (f j) = 0 := by
    intro j
    rw [hψC, hf]
    exact (RingHom.mem_ker).mp (hker ▸ Ideal.subset_span ⟨j, rfl⟩)
  -- lifts `λ` of the images of the variables in `Λ`
  choose lam hlam using fun i ↦ Ideal.Quotient.mk_surjective (v (φ (X i)))
  have hvC : ∀ p, v (ψC p) = Ideal.Quotient.mk _ (aeval lam p) := by
    intro p
    have : v.comp ψC = (Ideal.Quotient.mkₐ R _).comp (aeval lam) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, ψC, Ideal.Quotient.mkₐ_eq_mk, hlam]
    exact AlgHom.congr_fun this p
  have hμ : ∀ j, ∃ μ : Λ, aeval lam (f j) = algebraMap R Λ (ϖ ^ 2) * μ := by
    intro j
    have h1 : Ideal.Quotient.mk ((Ideal.span {ϖ ^ 2}).map (algebraMap R Λ)) (aeval lam (f j)) = 0 := by
      rw [← hvC, hfb', map_zero]
    exact mem_map_span_singleton_iff.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)
  choose μ hμ using hμ
  -- the algebra `D` and the map `ψ : D → Λ`
  let H₀ : MvPolynomial (Fin n ⊕ Fin m) R →ₐ[R] Λ :=
    aeval (Sum.elim lam fun j ↦ algebraMap R Λ ϖ * μ j)
  have hH₀ren : ∀ p, H₀ (rename Sum.inl p) = aeval lam p := fun p ↦ by
    rw [aeval_rename]
    rfl
  have hH₀C : ∀ x : R, H₀ (C x) = algebraMap R Λ x := fun x ↦ aeval_C _ _
  have hH₀z : ∀ j, H₀ (X (Sum.inr j)) = algebraMap R Λ ϖ * μ j := fun j ↦ by
    simp only [H₀, aeval_X, Sum.elim_inr]
  have hH₀E : ∀ ℓ, H₀ (relE ϖ f ℓ) = 0 := by
    intro ℓ
    rw [relE, map_sub, map_mul, hH₀ren, hμ, hH₀C, hH₀z, map_pow]
    ring
  have hH₀P : ∀ i ℓ, H₀ (relP ϖ f (charts i) ℓ) = 0 := by
    intro i ℓ
    obtain ⟨T, hT⟩ : ∃ T, T = aeval lam (charts i).a * μ ℓ -
        ∑ j, aeval lam ((charts i).h ℓ j) * μ ((charts i).e j) - aeval lam ((charts i).g ℓ) :=
      ⟨_, rfl⟩
    have h1 : H₀ (relP ϖ f (charts i) ℓ) = algebraMap R Λ ϖ * T := by
      rw [hT]
      simp only [relP, map_sub, map_mul, map_sum, hH₀ren, hH₀z, hH₀C, mul_sub, Finset.mul_sum]
      have e : ∀ j, aeval lam ((charts i).h ℓ j) * (algebraMap R Λ ϖ * μ ((charts i).e j)) =
          algebraMap R Λ ϖ * (aeval lam ((charts i).h ℓ j) * μ ((charts i).e j)) := fun j ↦ by ring
      simp only [e]
      ring
    have h2 : algebraMap R Λ ϖ ^ 2 * T = 0 := by
      have := congrArg (aeval lam) ((charts i).rel ℓ)
      simp only [map_add, map_mul, map_sum, hμ, aeval_C, map_pow] at this
      have e : ∑ x, aeval lam ((charts i).h ℓ x) * (algebraMap R Λ ϖ ^ 2 * μ ((charts i).e x)) =
          algebraMap R Λ ϖ ^ 2 * ∑ j, aeval lam ((charts i).h ℓ j) * μ ((charts i).e j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [e] at this
      rw [hT]
      linear_combination this
    rw [h1, hΛ T h2]
  have hKH : idealD charts ≤ RingHom.ker H₀ := by
    refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
    · rintro _ ⟨ℓ, rfl⟩
      exact hH₀E ℓ
    · rintro _ ⟨⟨i, ℓ⟩, rfl⟩
      exact hH₀P i ℓ
  let ψ : (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) →ₐ[R] Λ :=
    Ideal.Quotient.liftₐ (idealD charts) H₀ fun a ha ↦ hKH ha
  have hψ : ∀ x, ψ (Ideal.Quotient.mk (idealD charts) x) = H₀ x := fun _ ↦ rfl
  have hFP : Algebra.FinitePresentation R (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) :=
    Algebra.FinitePresentation.quotient (fg_idealD charts)
  -- the map `τ : C → D ⧸ ϖD`
  let J : Ideal (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) :=
    Ideal.span {algebraMap R _ ϖ}
  let τ₀ : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) ⧸ J :=
    (Ideal.Quotient.mkₐ R J).comp ((Ideal.Quotient.mkₐ R (idealD charts)).comp (rename Sum.inl))
  have hτ₀ : ∀ p, τ₀ p = Ideal.Quotient.mk J (Ideal.Quotient.mk (idealD charts) (rename Sum.inl p)) :=
    fun _ ↦ rfl
  have hϖD : Ideal.Quotient.mk (idealD charts) (C ϖ) = algebraMap R _ ϖ := by
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  have hτ₀f : ∀ j, τ₀ (f j) = 0 := by
    intro j
    rw [hτ₀, Ideal.Quotient.eq_zero_iff_mem]
    have : rename Sum.inl (f j) = relE ϖ f j + C ϖ * X (Sum.inr j) := by rw [relE]; ring
    rw [this, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr
      (show relE ϖ f j ∈ idealD charts from Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)),
      zero_add, map_mul, hϖD]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hτ₀ϖ : τ₀ (C (ϖ ^ 2)) = 0 := by
    rw [hτ₀, rename_C, Ideal.Quotient.eq_zero_iff_mem, map_pow, map_pow, hϖD, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hkerψC : RingHom.ker ψC.toRingHom ≤ RingHom.ker τ₀.toRingHom := by
    intro p hp
    have hp' : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) p ∈
        (Ideal.span (Set.range f)).map (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      have h1 : (⇑(MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))) ∘ f) = fb :=
        funext hf
      rw [h1, ← hker, RingHom.mem_ker, ← hψC]
      exact hp
    obtain ⟨p', hp'1, hp'2⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hp'
    have h2 : p - p' ∈ Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin n) R)} := by
      have : p - p' ∈ RingHom.ker
          (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))) := by
        rw [RingHom.mem_ker, map_sub, hp'2, sub_self]
      rwa [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at this
    have hle1 : Ideal.span (Set.range f) ≤ RingHom.ker τ₀.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hτ₀f j
    have hle2 : Ideal.span {(C (ϖ ^ 2) : MvPolynomial (Fin n) R)} ≤ RingHom.ker τ₀.toRingHom := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hτ₀ϖ
    have := Ideal.add_mem _ (hle1 hp'1) (hle2 h2)
    rwa [add_sub_cancel] at this
  have hkerψC' : ∀ x ∈ RingHom.ker ψC, τ₀ x = 0 := fun x hx ↦ hkerψC hx
  let τ' := Ideal.Quotient.liftₐ (RingHom.ker ψC) τ₀ hkerψC'
  obtain ⟨τ, hτ⟩ : ∃ τ : Cb →ₐ[R] (MvPolynomial (Fin n ⊕ Fin m) R ⧸ idealD charts) ⧸ J,
      ∀ p, τ (ψC p) = τ₀ p := by
    refine ⟨τ'.comp (Ideal.quotientKerAlgEquivOfSurjective hψCsurj).symm.toAlgHom, fun p ↦ ?_⟩
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  refine ⟨_, inferInstance, inferInstance, hFP, ψ, τ, ?_, ?_, ?_⟩
  · -- compatibility
    intro c d l hτc hvc
    obtain ⟨p, rfl⟩ := hψCsurj c
    rw [hτ, hτ₀, Ideal.Quotient.eq] at hτc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hτc
    rw [hvC, Ideal.Quotient.eq] at hvc
    obtain ⟨z₁, hz₁⟩ := mem_map_span_singleton_iff.mp hvc
    have h1 := congrArg ψ hw
    rw [map_mul, map_sub, hψ, hH₀ren, AlgHom.commutes] at h1
    refine ⟨ψ w - algebraMap R Λ ϖ * z₁, ?_⟩
    rw [map_pow] at hz₁
    linear_combination -h1 - hz₁
  · -- smoothness away from `ϖ`
    intro q _ hq
    apply isSmoothAt_D_of_notMem charts q
    rw [hϖD]
    exact hq
  · -- smoothness on the charts
    intro y hy l hl 𝔭 _ hπ hl𝔭
    obtain ⟨N, hN⟩ := hrad y hy
    have hex : ∃ i, aeval lam (A i * Matrix.det (Matrix.of fun j l : Fin (cc i) ↦
        pderiv (uu i l) (f (ee i j)))) ∉ 𝔭 := by
      by_contra hall
      push Not at hall
      obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun Cb).mp hN
      have h1 : ∀ i, v (φ (aa i * Matrix.det (Matrix.of fun j l : Fin (cc i) ↦
          pderiv (uu i l) (fb (ee i j))))) = Ideal.Quotient.mk _ (aeval lam (A i *
            Matrix.det (Matrix.of fun j l : Fin (cc i) ↦ pderiv (uu i l) (f (ee i j))))) := by
        intro i
        have hmap : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) (A i *
            Matrix.det (Matrix.of fun j l : Fin (cc i) ↦ pderiv (uu i l) (f (ee i j)))) =
            aa i * Matrix.det (Matrix.of fun j l : Fin (cc i) ↦ pderiv (uu i l) (fb (ee i j))) := by
          rw [map_mul, hA, RingHom.map_det]
          congr 2
          ext j l
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ← pderiv_map, hf]
        rw [← hvC, hψC, hmap]
      choose β hβ using fun i ↦ Ideal.Quotient.mk_surjective (v (b i))
      have h2 : l ^ N - ∑ i, β i * aeval lam (A i * Matrix.det (Matrix.of fun j l : Fin (cc i) ↦
          pderiv (uu i l) (f (ee i j)))) ∈ (Ideal.span {ϖ ^ 2}).map (algebraMap R Λ) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_sum, ← hl, ← map_pow, ← hb,
          map_sum, sub_eq_zero]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [smul_eq_mul, map_mul, h1, ← hβ, ← map_mul]
      have h3 : (Ideal.span {ϖ ^ 2}).map (algebraMap R Λ) ≤ 𝔭 := by
        rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
        show algebraMap R Λ (ϖ ^ 2) ∈ 𝔭
        rw [map_pow]
        exact Ideal.pow_mem_of_mem _ hπ _ two_pos
      have h4 : l ^ N ∈ 𝔭 := by
        have hs : ∑ i, β i * aeval lam (A i * Matrix.det (Matrix.of fun j l : Fin (cc i) ↦
            pderiv (uu i l) (f (ee i j)))) ∈ 𝔭 :=
          Ideal.sum_mem _ fun i _ ↦ 𝔭.mul_mem_left (β i) (hall i)
        have := 𝔭.add_mem (h3 h2) hs
        rwa [sub_add_cancel] at this
      exact hl𝔭 ((inferInstance : 𝔭.IsPrime).mem_of_pow_mem _ h4)
    obtain ⟨i, hi⟩ := hex
    apply isSmoothAt_D_of_chart hR charts i
    show ψ (Ideal.Quotient.mk (idealD charts) _) ∉ 𝔭
    rw [hψ, hH₀ren]
    exact hi

end Main

end Langlands.CommutativeAlgebra.Popescu.Desing
