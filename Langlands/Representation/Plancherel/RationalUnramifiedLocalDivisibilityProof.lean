import Langlands.Representation.Plancherel.RationalUnramifiedLocalDivisibilityStatement
import Langlands.Representation.Plancherel.RationalUnramifiedDensity
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Proof of local hypersurface divisibility for actual unramified regular scalars -/

noncomputable section

open Polynomial

namespace Langlands.Plancherel

universe u

/-- A monic irreducible polynomial over an integrally closed domain that does
not divide `B` satisfies a Bezout identity with `B` up to a nonzero constant. -/
theorem polynomial_exists_mul_add_mul_eq_C_of_not_dvd {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] {Q B : R[X]} (hQ : Q.Monic) (hirr : Irreducible Q)
    (hdvd : ¬ Q ∣ B) :
    ∃ r : R, r ≠ 0 ∧ ∃ u v : R[X], u * Q + v * B = C r := by
  classical
  let K := FractionRing R
  have hinj : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hirrK : Irreducible (Q.map (algebraMap R K)) :=
    (hQ.irreducible_iff_irreducible_map_fraction_map).mp hirr
  have hndK : ¬ Q.map (algebraMap R K) ∣ B.map (algebraMap R K) := by
    intro h
    apply hdvd
    rw [← modByMonic_eq_zero_iff_dvd hQ]
    apply hinj
    rw [Polynomial.map_zero, map_modByMonic _ hQ, modByMonic_eq_zero_iff_dvd (hQ.map _)]
    exact h
  obtain ⟨U, V, hUV⟩ := (hirrK.coprime_iff_not_dvd).mpr hndK
  obtain ⟨b1, hb1, hU⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) U
  obtain ⟨b2, hb2, hV⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) V
  refine ⟨b1 * b2, mul_ne_zero (nonZeroDivisors.ne_zero hb1) (nonZeroDivisors.ne_zero hb2),
    C b2 * IsLocalization.integerNormalization (nonZeroDivisors R) U,
    C b1 * IsLocalization.integerNormalization (nonZeroDivisors R) V, ?_⟩
  apply hinj
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hU, hV,
    Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
  linear_combination (C (algebraMap R K b1) * C (algebraMap R K b2)) * hUV

/-- A monic complex polynomial whose value at `t₀` is smaller than `ε ^ degree`
has a root within distance `ε` of `t₀`. -/
theorem complexPolynomial_exists_mem_roots_norm_sub_lt {q : ℂ[X]} (hq : q.Monic) (t₀ : ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ‖q.eval t₀‖ < ε ^ q.natDegree) :
    ∃ t ∈ q.roots, ‖t₀ - t‖ < ε := by
  by_contra! hcon
  have hle := Multiset.prod_map_le_prod_map₀ (fun _ => ε) (fun t => ‖t₀ - t‖)
    (fun _ _ => hε) hcon
  have heq : (q.roots.map fun t => ‖t₀ - t‖).prod = ‖q.eval t₀‖ := by
    rw [(IsAlgClosed.splits q).eval_eq_prod_roots_of_monic hq]
    change _ = NormedField.toMulRingNorm ℂ _
    rw [← Multiset.prod_hom' q.roots (NormedField.toMulRingNorm ℂ) (fun t => t₀ - t)]
    rfl
  simp only [Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree] at hle
  linarith

/-- A nonzero complex multivariable polynomial has a nonzero value on every
nonempty open set. -/
theorem mvPolynomial_exists_eval_ne_zero_of_isOpen {σ : Type*} [Finite σ]
    {r : MvPolynomial σ ℂ} (hr : r ≠ 0) {W : Set (σ → ℂ)} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ s ∈ W, MvPolynomial.eval s r ≠ 0 := by
  by_contra! h
  obtain ⟨s₀, hs₀⟩ := hne
  obtain ⟨S, hS, hSW⟩ := isOpen_pi_iff'.mp hW s₀ hs₀
  apply hr
  apply MvPolynomial.funext_set S
    (fun i => infinite_of_mem_nhds (s₀ i) ((hS i).1.mem_nhds (hS i).2))
  intro x hx
  simp [h x (hSW hx)]

/-- Root continuity for a monic polynomial over the next variables: near a zero
of `Q`, there is a zero of `Q` where the Bezout constant `r` is nonzero, hence
where `B` is nonzero. -/
theorem monicFiber_exists_zero_eval_ne_zero {m : ℕ}
    {Q B u v : (MvPolynomial (Fin m) ℂ)[X]} {r : MvPolynomial (Fin m) ℂ}
    (hQ : Q.Monic) (hr : r ≠ 0) (huv : u * Q + v * B = C r)
    {V : Set (Fin (m + 1) → ℂ)} (hV : IsOpen V) (t₀ : ℂ) (s₀ : Fin m → ℂ)
    (hy₀ : (Fin.cons t₀ s₀ : Fin (m + 1) → ℂ) ∈ V)
    (hQ₀ : (Q.map (MvPolynomial.eval s₀)).eval t₀ = 0) :
    ∃ (t : ℂ) (s : Fin m → ℂ), (Fin.cons t s : Fin (m + 1) → ℂ) ∈ V ∧
      (Q.map (MvPolynomial.eval s)).eval t = 0 ∧
      (B.map (MvPolynomial.eval s)).eval t ≠ 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV _ hy₀
  have hcont : Continuous fun s : Fin m → ℂ => (Q.map (MvPolynomial.eval s)).eval t₀ := by
    have h := (MvPolynomial.continuous_eval ((MvPolynomial.finSuccEquiv ℂ m).symm Q)).comp
      ((continuous_const (y := t₀)).finCons continuous_id)
    convert h using 2 with s
    simp [Function.comp, MvPolynomial.eval_eq_eval_mv_eval']
  let W : Set (Fin m → ℂ) :=
    {s | ‖(Q.map (MvPolynomial.eval s)).eval t₀‖ < δ ^ Q.natDegree} ∩ Metric.ball s₀ δ
  have hWo : IsOpen W :=
    (isOpen_lt (continuous_norm.comp hcont) continuous_const).inter Metric.isOpen_ball
  have hWne : W.Nonempty := ⟨s₀, by simp [W, hQ₀, hδ, pow_pos]⟩
  obtain ⟨s, ⟨hsQ, hsball⟩, hrs⟩ := mvPolynomial_exists_eval_ne_zero_of_isOpen hr hWo hWne
  have hmon : (Q.map (MvPolynomial.eval s)).Monic := hQ.map _
  obtain ⟨t, ht, htt⟩ := complexPolynomial_exists_mem_roots_norm_sub_lt hmon t₀ hδ.le
    (by rwa [hQ.natDegree_map])
  have hroot : (Q.map (MvPolynomial.eval s)).eval t = 0 :=
    (mem_roots hmon.ne_zero).mp ht
  refine ⟨t, s, hball ?_, hroot, ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [dist_eq_norm, norm_sub_rev] using htt
    · simp only [Fin.cons_succ]
      exact (dist_le_pi_dist s s₀ j).trans_lt hsball
  · intro hB
    have h := congrArg (fun f => (f.map (MvPolynomial.eval s)).eval t) huv
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hroot, hB,
      Polynomial.map_C, eval_C, mul_zero, add_zero] at h
    exact hrs h.symm

/-! ### Nagata's change of variables

The declarations of this section reproduce, under new names, auxiliary lemmas
that are private in Mathlib's `Mathlib/RingTheory/NoetherNormalization.lean`
(Copyright (c) 2025 Sihan Su; authors Riccardo Brasca, Sihan Su, Wan Lin,
Xiaoyang Su; released under the Apache 2.0 license). The algebra map
`NoetherNormalization.T1` itself is public there. -/

section Nagata

open MvPolynomial Ideal Nat RingHom List NoetherNormalization

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

variable {f v} in
theorem nagata_lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

theorem nagata_t1_comp_t1_neg (c : k) :
    (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

theorem nagata_t1_injective : Function.Injective (T1 f 1) := by
  intro p q h
  have h' := congrArg (T1 f (-1)) h
  simpa only [← AlgHom.comp_apply, (by simpa using nagata_t1_comp_t1_neg f (-1) :
    (T1 f (-1)).comp (T1 f 1) = AlgHom.id _ _),
    AlgHom.id_apply] using h'

theorem nagata_sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (nagata_lt_up vlt) (nagata_lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

theorem nagata_degreeOf_zero_t {a : k} (ha : a ≠ 0) :
    (T1 f 1 (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, ite_eq_left,
    Fin.succ_ne_zero, ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

theorem nagata_degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T1 f 1 <| monomial v <| f.coeff v).degreeOf 0 ≠
    (T1 f 1 <| monomial w <| f.coeff w).degreeOf 0 := by
  rw [nagata_degreeOf_zero_t _ _ <| mem_support_iff.mp hv,
    nagata_degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine nagata_sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

theorem nagata_leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n <| T1 f 1 <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 :=
        fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, ite_eq_right h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- Nagata's automorphism makes a nonzero polynomial have invertible leading
coefficient in the variable `X₀`. -/
theorem nagata_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T1 f 1 f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T1 f 1 <| monomial v <| f.coeff v).degreeOf 0)
    (support_nonempty.mpr fne)
  set h := fun w ↦ MvPolynomial.monomial w (f.coeff w)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n (T1 f 1 (h x))).degree <
      (finSuccEquiv k n (T1 f 1 (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using nagata_degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T1 f 1)
      (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n (T1 f 1 (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n (T1 f 1 (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _),
        map_eq_zero_iff _ (nagata_t1_injective f)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [nagata_leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, MvPolynomial.algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end Nagata

/-- Evaluation after a complex algebra map of polynomial rings is evaluation at
the images of the variables. -/
theorem mvPolynomial_eval_algHom {σ τ : Type*}
    (T : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (y : τ → ℂ) (h : MvPolynomial σ ℂ) :
    MvPolynomial.eval y (T h) =
      MvPolynomial.eval (fun i => MvPolynomial.eval y (T (MvPolynomial.X i))) h := by
  have hcomp : (MvPolynomial.aeval y).comp T =
      MvPolynomial.aeval (fun i => MvPolynomial.eval y (T (MvPolynomial.X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have h2 := congrArg (fun F => F h) hcomp
  simpa [MvPolynomial.coe_aeval_eq_eval] using h2

/-- Polynomial form of local hypersurface divisibility: an irreducible complex
polynomial with a zero in an open set, not dividing `A`, has a zero in that set
where `A` is nonzero. -/
theorem mvPolynomial_exists_zero_eval_ne_zero {n : ℕ} {P A : MvPolynomial (Fin n) ℂ}
    (hP : Irreducible P) (hPA : ¬ P ∣ A) {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ V) (hPz₀ : MvPolynomial.eval z₀ P = 0) :
    ∃ z ∈ V, MvPolynomial.eval z P = 0 ∧ MvPolynomial.eval z A ≠ 0 := by
  cases n with
  | zero =>
    exfalso
    apply hP.ne_zero
    apply MvPolynomial.funext
    intro x
    rw [Subsingleton.elim x z₀, hPz₀, map_zero]
  | succ m =>
    let e : MvPolynomial (Fin (m + 1)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
      AlgEquiv.ofAlgHom (NoetherNormalization.T1 P 1) (NoetherNormalization.T1 P (-1))
        (nagata_t1_comp_t1_neg P 1) (by simpa using nagata_t1_comp_t1_neg P (-1))
    let ψ := MvPolynomial.finSuccEquiv ℂ m
    have hu : IsUnit (ψ (e P)).leadingCoeff := nagata_leadingCoeff_isUnit P hP.ne_zero
    let w : MvPolynomial (Fin m) ℂ := ↑hu.unit⁻¹
    have hwu : IsUnit w := Units.isUnit _
    let Q := C w * ψ (e P)
    let B := ψ (e A)
    have hQm : Q.Monic := by
      rw [Monic, leadingCoeff_mul, leadingCoeff_C]
      exact hu.val_inv_mul
    have hP' : Irreducible (ψ (e P)) := by
      have h0 : Irreducible ((e.trans ψ).toRingEquiv.toMulEquiv P) :=
        (MulEquiv.irreducible_iff (e.trans ψ).toRingEquiv.toMulEquiv).mpr hP
      exact h0
    have hQi : Irreducible Q :=
      (irreducible_isUnit_mul (isUnit_C.mpr hwu)).mpr hP'
    have hQB : ¬ Q ∣ B := by
      intro h
      apply hPA
      have h1 : (e.trans ψ) P ∣ (e.trans ψ) A := (dvd_mul_left _ _).trans h
      simpa using map_dvd (e.trans ψ).symm h1
    obtain ⟨r, hr, u, v, huv⟩ := polynomial_exists_mul_add_mul_eq_C_of_not_dvd hQm hQi hQB
    let φ : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ) :=
      fun y i => MvPolynomial.eval y (e (MvPolynomial.X i))
    let φ' : (Fin (m + 1) → ℂ) → (Fin (m + 1) → ℂ) :=
      fun y i => MvPolynomial.eval y (e.symm (MvPolynomial.X i))
    have heval (y : Fin (m + 1) → ℂ) (h : MvPolynomial (Fin (m + 1)) ℂ) :
        MvPolynomial.eval y (e h) = MvPolynomial.eval (φ y) h :=
      mvPolynomial_eval_algHom e.toAlgHom y h
    have heval' (y : Fin (m + 1) → ℂ) (h : MvPolynomial (Fin (m + 1)) ℂ) :
        MvPolynomial.eval y (e.symm h) = MvPolynomial.eval (φ' y) h :=
      mvPolynomial_eval_algHom e.symm.toAlgHom y h
    have hφφ' (y : Fin (m + 1) → ℂ) : φ (φ' y) = y := by
      funext i
      change MvPolynomial.eval (φ' y) (e (MvPolynomial.X i)) = y i
      rw [← heval', AlgEquiv.symm_apply_apply, MvPolynomial.eval_X]
    have hφc : Continuous φ := continuous_pi fun i => MvPolynomial.continuous_eval _
    have hQev (t : ℂ) (s : Fin m → ℂ) :
        (Q.map (MvPolynomial.eval s)).eval t =
          MvPolynomial.eval s w * MvPolynomial.eval (φ (Fin.cons t s)) P := by
      simp only [Q, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C]
      rw [← MvPolynomial.eval_eq_eval_mv_eval', heval]
    have hBev (t : ℂ) (s : Fin m → ℂ) :
        (B.map (MvPolynomial.eval s)).eval t = MvPolynomial.eval (φ (Fin.cons t s)) A := by
      simp only [B]
      rw [← MvPolynomial.eval_eq_eval_mv_eval', heval]
    have hw (s : Fin m → ℂ) : MvPolynomial.eval s w ≠ 0 :=
      (hwu.map (MvPolynomial.eval s)).ne_zero
    let y₀ := φ' z₀
    have hy₀ : (Fin.cons (y₀ 0) (Fin.tail y₀) : Fin (m + 1) → ℂ) = y₀ := Fin.cons_self_tail y₀
    obtain ⟨t, s, hV', hQ0, hB0⟩ := monicFiber_exists_zero_eval_ne_zero hQm hr huv
      (hV.preimage hφc) (y₀ 0) (Fin.tail y₀)
      (by rw [Set.mem_preimage, hy₀, hφφ']; exact hz₀)
      (by rw [hQev, hy₀, hφφ', hPz₀, mul_zero])
    refine ⟨φ (Fin.cons t s), hV', ?_, ?_⟩
    · rw [hQev] at hQ0
      exact (mul_eq_zero.mp hQ0).resolve_left (hw s)
    · rwa [hBev] at hB0

/-- Laurent form of local hypersurface divisibility: an irreducible finite
Laurent combination with a zero in an open set of the complex torus, not
dividing `a`, has a zero in that set where `a` is nonzero. -/
theorem finiteLaurent_exists_zero_eval_ne_zero {n : ℕ}
    {p a : AddMonoidAlgebra ℂ (Fin n → ℤ)} (hp : Irreducible p) (hpa : ¬ p ∣ a)
    {V : Set (Fin n → ℂˣ)} (hV : IsOpen V) {c₀ : Fin n → ℂˣ} (hc₀ : c₀ ∈ V)
    (hpc₀ : finiteLaurentEvaluation c₀ p = 0) :
    ∃ c ∈ V, finiteLaurentEvaluation c p = 0 ∧ finiteLaurentEvaluation c a ≠ 0 := by
  classical
  let κ : (Fin n →₀ ℕ) →+ (Fin n → ℤ) :=
    Finsupp.coeFnAddHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  let ι : MvPolynomial (Fin n) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ (Fin n → ℤ) :=
    AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ κ
  have hι (d : Fin n →₀ ℕ) (b : ℂ) :
      ι (MvPolynomial.monomial d b) = AddMonoidAlgebra.single (fun i => (d i : ℤ)) b := by
    rw [← MvPolynomial.single_eq_monomial]
    simp only [ι, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    congr 1
  have hιev (c : Fin n → ℂˣ) (F : MvPolynomial (Fin n) ℂ) :
      finiteLaurentEvaluation c (ι F) = MvPolynomial.eval (fun i => (c i : ℂ)) F := by
    induction F using MvPolynomial.induction_on' with
    | monomial d b =>
      rw [hι, finiteLaurentEvaluation_single, MvPolynomial.eval_monomial,
        Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
      simp
    | add F G hF hG => rw [map_add, map_add, map_add, hF, hG]
  have hclear (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
      ∃ (N : Fin n →₀ ℕ) (F : MvPolynomial (Fin n) ℂ),
        AddMonoidAlgebra.single (fun i => (N i : ℤ)) 1 * f = ι F := by
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, 0, by simp⟩
    | add f g hf hg =>
      obtain ⟨N₁, F₁, h₁⟩ := hf
      obtain ⟨N₂, F₂, h₂⟩ := hg
      refine ⟨N₁ + N₂, MvPolynomial.monomial N₂ 1 * F₁ + MvPolynomial.monomial N₁ 1 * F₂, ?_⟩
      rw [map_add, map_mul, map_mul, hι, hι, ← h₁, ← h₂]
      have hs : AddMonoidAlgebra.single (fun i => ((N₁ + N₂) i : ℤ)) (1 : ℂ) =
          AddMonoidAlgebra.single (fun i => (N₁ i : ℤ)) 1 *
            AddMonoidAlgebra.single (fun i => (N₂ i : ℤ)) 1 := by
        rw [AddMonoidAlgebra.single_mul_single, one_mul]
        congr 1
      rw [hs]
      ring
    | single m b =>
      refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (-m i).toNat),
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => (m i).toNat)) b, ?_⟩
      rw [hι, AddMonoidAlgebra.single_mul_single, one_mul]
      congr 1
      funext i
      simp only [Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
      omega
  have hunit (N : Fin n →₀ ℕ) :
      IsUnit (AddMonoidAlgebra.single (fun i => (N i : ℤ)) (1 : ℂ)) := by
    refine isUnit_iff_exists_inv.mpr ⟨AddMonoidAlgebra.single (-fun i => (N i : ℤ)) 1, ?_⟩
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_neg_cancel]
    rfl
  obtain ⟨Np, P, hP⟩ := hclear p
  obtain ⟨Na, A, hA⟩ := hclear a
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at hP
    exact hp.ne_zero (((hunit Np).mul_right_eq_zero).mp hP)
  -- an irreducible factor `q` of `P` vanishing at `c₀`
  have hPc₀ : MvPolynomial.eval (fun i => (c₀ i : ℂ)) P = 0 := by
    rw [← hιev, ← hP, map_mul, hpc₀, mul_zero]
  obtain ⟨q, hqf, hqc₀⟩ : ∃ q ∈ UniqueFactorizationMonoid.factors P,
      MvPolynomial.eval (fun i => (c₀ i : ℂ)) q = 0 := by
    obtain ⟨w, hw⟩ := UniqueFactorizationMonoid.factors_prod hP0
    have h := congrArg (MvPolynomial.eval fun i => (c₀ i : ℂ)) hw
    rw [map_mul, hPc₀, mul_eq_zero, map_multiset_prod, Multiset.prod_eq_zero_iff] at h
    rcases h with h | h
    · obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.mp h
      exact ⟨q, hq, hq0⟩
    · exact absurd h (w.isUnit.map _).ne_zero
  have hq : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hqf
  have hqP : q ∣ P := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
  -- `p` is associated to the image of `q`
  have hqp : ι q ∣ p := by
    have h1 : ι q ∣ AddMonoidAlgebra.single (fun i => (Np i : ℤ)) 1 * p := hP ▸ map_dvd ι hqP
    exact (hunit Np).dvd_mul_left.mp h1
  obtain ⟨k, hk⟩ := hqp
  have hku : IsUnit k := by
    rcases hp.isUnit_or_isUnit hk with h | h
    · exfalso
      have h2 := (h.map (finiteLaurentEvaluation c₀)).ne_zero
      rw [hιev] at h2
      exact h2 hqc₀
    · exact h
  have hassoc : Associated (ι q) p := ⟨hku.unit, hk.symm⟩
  have hqA : ¬ q ∣ A := by
    intro h
    apply hpa
    have h1 : ι q ∣ AddMonoidAlgebra.single (fun i => (Na i : ℤ)) 1 * a := hA ▸ map_dvd ι h
    exact hassoc.symm.dvd.trans ((hunit Na).dvd_mul_left.mp h1)
  -- transfer to the open image of `V` in `Fin n → ℂ`
  let φ : (Fin n → ℂˣ) → (Fin n → ℂ) := Pi.map fun _ => Units.val
  have hφ : IsOpenMap φ :=
    IsOpenMap.piMap (fun _ => IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap)
      (by rw [Filter.cofinite_eq_bot]; exact Filter.eventually_bot)
  obtain ⟨z, ⟨c, hcV, rfl⟩, hqz, hAz⟩ :=
    mvPolynomial_exists_zero_eval_ne_zero hq hqA (hφ V hV) ⟨c₀, hc₀, rfl⟩ hqc₀
  refine ⟨c, hcV, ?_, ?_⟩
  · rw [hk, map_mul, hιev]
    change MvPolynomial.eval (φ c) q * _ = 0
    rw [hqz, zero_mul]
  · intro hac
    apply hAz
    change MvPolynomial.eval (fun i => (c i : ℂ)) A = 0
    rw [← hιev, ← hA, map_mul, hac, mul_zero]

section ActualCharacters

open scoped CategoryTheory.MonObj

/-- Local hypersurface divisibility for actual unramified regular scalars. -/
theorem rationalUnramifiedLocalHypersurfaceDivisibility :
    RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u} := by
  intro F _ _ _ _ G _ hp hG U p a hU hirr ⟨χ₀, hχ₀, hpχ₀⟩ hvan
  by_contra hdvd
  let e := (rationalImageUnramifiedContinuousEquiv G hp).symm.trans
    (rationalReductiveImageCharacterCoordinates G hG)
  let α := rationalUnramifiedLaurentAlgebraEquiv G hp hG
  have hev (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
      (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
      b.val χ = finiteLaurentEvaluation (e χ) (α.symm b) := by
    have h := rationalUnramifiedLaurentAlgebraEquiv_eval G hp hG (α.symm b) χ
    rw [α.apply_symm_apply] at h
    exact h
  have hirr' : Irreducible (α.symm p) :=
    (MulEquiv.irreducible_iff α.symm.toRingEquiv.toMulEquiv).mpr hirr
  have hdvd' : ¬ α.symm p ∣ α.symm a := by
    intro h
    have h' := map_dvd α h
    rw [α.apply_symm_apply, α.apply_symm_apply] at h'
    exact hdvd h'
  have hχ₀' : e χ₀ ∈ e.symm ⁻¹' U := by
    rw [Set.mem_preimage, e.symm_apply_apply]
    exact hχ₀
  obtain ⟨c, hcV, hpc, hac⟩ := finiteLaurent_exists_zero_eval_ne_zero hirr' hdvd'
    (hU.preimage e.symm.continuous) hχ₀' (by rw [← hev]; exact hpχ₀)
  apply hac
  have h := hvan (e.symm c) hcV (by rw [hev, e.apply_symm_apply]; exact hpc)
  rwa [hev, e.apply_symm_apply] at h

end ActualCharacters

end Langlands.Plancherel
