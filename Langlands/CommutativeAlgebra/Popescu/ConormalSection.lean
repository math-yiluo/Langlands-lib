import Langlands.MathlibBase

/-! # A section of the conormal sequence after inverting a smooth element -/

namespace Langlands.CommutativeAlgebra.Popescu.SymRetract

open MvPolynomial

/-- Taylor expansion to first order at a point perturbed by a square-zero family. -/
theorem aeval_add_of_sqZero {R T σ : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Fintype σ] [DecidableEq σ] (t δ : σ → T) (hδ : ∀ i j, δ i * δ j = 0)
    (p : MvPolynomial σ R) :
    aeval (t + δ) p = aeval t p + ∑ i, aeval t (pderiv i p) * δ i := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p v hp =>
    have hsum : ∑ i, aeval t (pderiv i (p * X v)) * δ i =
        (∑ i, aeval t (pderiv i p) * δ i) * t v + aeval t p * δ v := by
      have h : ∀ i, pderiv i (p * X v) = pderiv i p * X v + p * pderiv i (X v) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      simp only [h, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · rw [Finset.sum_eq_single v]
        · rw [pderiv_X_self, map_one, mul_one]
        · intro i _ hi
          rw [pderiv_X_of_ne (Ne.symm hi), map_zero, mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ v) h
    have h1 : (∑ i, aeval t (pderiv i p) * δ i) * δ v = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hδ, mul_zero]
    rw [map_mul, map_mul, aeval_X, aeval_X, hp, hsum, Pi.add_apply]
    linear_combination h1

section

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}

/-- The ideal `I_h = I · R[x]_h` of `R[x]_h`, where `I = ker φ`. -/
noncomputable abbrev locKer (φ : MvPolynomial (Fin n) R →ₐ[R] B) (h : MvPolynomial (Fin n) R) :
    Ideal (Localization.Away h) :=
  (RingHom.ker φ).map (algebraMap _ _)

end

/-- The localized form of `exists_conormal_section`: over `R[x]_h`, each `f_k` is congruent modulo
`I_h²` to `-Σ_i ∂f_k/∂x_i · θ_i` with `θ_i = Σ_l c_il f_l ∈ I_h`. -/
theorem exists_conormal_section_loc {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {n m : ℕ} (φ : MvPolynomial (Fin n) R →ₐ[R] B) (hφ : Function.Surjective φ)
    (f : Fin m → MvPolynomial (Fin n) R) (hker : RingHom.ker φ = Ideal.span (Set.range f))
    (h : MvPolynomial (Fin n) R) [Algebra.FormallySmooth R (Localization.Away (φ h))] :
    ∃ c : Fin n → Fin m → Localization.Away h, ∀ k,
      algebraMap _ (Localization.Away h) (f k) + ∑ i, algebraMap _ _ (pderiv i (f k)) *
        ∑ l, c i l * algebraMap _ _ (f l) ∈ locKer φ h ^ 2 := by
  classical
  -- the square-zero extension `R[x]_h/I_h² → R[x]_h/I_h`
  have hle : locKer φ h ^ 2 ≤ locKer φ h := Ideal.pow_le_self two_ne_zero
  let q : (Localization.Away h ⧸ locKer φ h ^ 2) →ₐ[R] (Localization.Away h ⧸ locKer φ h) :=
    Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ R _) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha))
  have hq : ∀ y, q (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y := fun y => rfl
  have hqs : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ y, hq y⟩
  have hqker : RingHom.ker q.toRingHom ≤ (locKer φ h).map (Ideal.Quotient.mk _) := by
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : Ideal.Quotient.mk (locKer φ h) y = 0 := hz
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp this)
  have hsq : ((locKer φ h).map (Ideal.Quotient.mk (locKer φ h ^ 2))) ^ 2 = ⊥ :=
    (Ideal.map_pow (Ideal.Quotient.mk (locKer φ h ^ 2)) (locKer φ h) 2).symm.trans
      (Ideal.map_quotient_self _)
  have hqnil : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, eq_bot_iff.mpr ?_⟩
    rw [← hsq]
    exact Ideal.pow_right_mono hqker 2
  -- the map `B_a → R[x]_h/I_h`
  let ψ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away h ⧸ locKer φ h :=
    (Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) _)
  have hψ : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    intro p hp
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (algebraMap _ (Localization.Away h) p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hp)
  let g₀ : B →ₐ[R] Localization.Away h ⧸ locKer φ h := AlgHom.liftOfSurjective φ hφ ψ hψ
  have hg₀ : ∀ p, g₀ (φ p) = ψ p := fun p => AlgHom.liftOfSurjective_apply φ hφ ψ hψ p
  have hu : IsUnit (g₀.toRingHom (φ h)) := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hg₀]
    exact (IsLocalization.Away.algebraMap_isUnit h).map (Ideal.Quotient.mk _)
  let g₁ : Localization.Away (φ h) →+* Localization.Away h ⧸ locKer φ h :=
    IsLocalization.Away.lift (φ h) (g := g₀.toRingHom) hu
  have hg₁ : ∀ b : B, g₁ (algebraMap B _ b) = g₀ b := fun b =>
    IsLocalization.Away.lift_eq (φ h) hu b
  let g : Localization.Away (φ h) →ₐ[R] Localization.Away h ⧸ locKer φ h :=
    { toRingHom := g₁
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R B (Localization.Away (φ h))]
        exact (hg₁ _).trans (g₀.commutes r) }
  have hg : ∀ b : B, g (algebraMap B _ b) = g₀ b := hg₁
  -- the lift
  let s := Algebra.FormallySmooth.liftOfSurjective g q hqs hqnil
  have hs : ∀ y, q (s y) = g y := Algebra.FormallySmooth.liftOfSurjective_apply g q hqs hqnil
  let xT : Fin n → Localization.Away h ⧸ locKer φ h ^ 2 := fun i =>
    Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h) (X i))
  let θ : Fin n → Localization.Away h ⧸ locKer φ h ^ 2 := fun i =>
    s (algebraMap B _ (φ (X i))) - xT i
  have hθJ : ∀ i, θ i ∈ (locKer φ h).map (Ideal.Quotient.mk (locKer φ h ^ 2)) := fun i => by
    apply hqker
    rw [RingHom.mem_ker]
    change q (θ i) = 0
    rw [map_sub, hs, hg, hg₀]
    exact sub_self _
  have hsq2 : (locKer φ h).map (Ideal.Quotient.mk (locKer φ h ^ 2)) *
      (locKer φ h).map (Ideal.Quotient.mk (locKer φ h ^ 2)) = ⊥ := (pow_two _).symm.trans hsq
  have hθθ : ∀ i j, θ i * θ j = 0 := fun i j => by
    have := Ideal.mul_mem_mul (hθJ i) (hθJ j)
    rwa [hsq2, Ideal.mem_bot] at this
  -- the composite `R[x] → R[x]_h/I_h²` and Taylor expansion
  have hcomp : ∀ p : MvPolynomial (Fin n) R, s (algebraMap B _ (φ p)) = aeval (xT + θ) p := by
    intro p
    have : ((s.comp (IsScalarTower.toAlgHom R B (Localization.Away (φ h)))).comp φ) =
        aeval (xT + θ) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [θ]
    exact AlgHom.congr_fun this p
  have hxT : ∀ p : MvPolynomial (Fin n) R, aeval xT p =
      Ideal.Quotient.mk _ (algebraMap _ (Localization.Away h) p) := by
    intro p
    have : aeval xT = (Ideal.Quotient.mkₐ R (locKer φ h ^ 2)).comp
        (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) (Localization.Away h)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [xT]
    exact AlgHom.congr_fun this p
  have hkey : ∀ k, Ideal.Quotient.mk (locKer φ h ^ 2) (algebraMap _ _ (f k)) +
      ∑ i, Ideal.Quotient.mk (locKer φ h ^ 2) (algebraMap _ _ (pderiv i (f k))) * θ i = 0 := by
    intro k
    have h0 : φ (f k) = 0 := by
      show f k ∈ RingHom.ker φ
      rw [hker]; exact Ideal.subset_span ⟨k, rfl⟩
    have := hcomp (f k)
    rw [h0, map_zero, map_zero, aeval_add_of_sqZero xT θ hθθ] at this
    simp only [hxT] at this
    exact this.symm
  -- writing `θ` in terms of the `f`
  have hIL : locKer φ h = Ideal.span (Set.range fun l => algebraMap _ (Localization.Away h) (f l)) := by
    simp only [locKer, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hθ' : ∀ i, ∃ c : Fin m → Localization.Away h, θ i = Ideal.Quotient.mk (locKer φ h ^ 2)
      (∑ l, c l * algebraMap _ _ (f l)) := by
    intro i
    obtain ⟨y, hy, hyθ⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      (hθJ i)
    rw [hIL] at hy
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hy
    exact ⟨c, by rw [← hyθ, ← hc]⟩
  choose c hc using hθ'
  refine ⟨c, fun k => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := hkey k
  simp only [hc] at this
  rw [map_add, map_sum]
  simpa only [map_mul] using this

set_option maxHeartbeats 400000 in
/-- Let `B = R[x_1, …, x_n]/(f_1, …, f_m)` and let `h` be a polynomial whose image `a` in `B` has
`B_a` formally smooth over `R`. Then the conormal map `I/I² → ⊕ B dxᵢ` has a section after
inverting `a`. Concretely, for some `t` and some matrix `P` of polynomials,
`h^t f_k ≡ Σ_l (Σ_i ∂f_k/∂x_i · P_il) f_l` modulo `I²`, where `I = (f_1, …, f_m)`. -/
theorem exists_conormal_section {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {n m : ℕ}
    (φ : MvPolynomial (Fin n) R →ₐ[R] B) (hφ : Function.Surjective φ)
    (f : Fin m → MvPolynomial (Fin n) R) (hker : RingHom.ker φ = Ideal.span (Set.range f))
    (h : MvPolynomial (Fin n) R) [Algebra.FormallySmooth R (Localization.Away (φ h))] :
    ∃ (t : ℕ) (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R)), ∀ k,
      h ^ t * f k - ∑ l, (∑ i, pderiv i (f k) * P i l) * f l ∈ RingHom.ker φ ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := exists_conormal_section_loc φ hφ f hker h
  -- clearing denominators
  obtain ⟨⟨b, hb⟩, hbc⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers h)
    (Finset.univ : Finset (Fin n × Fin m)) (fun il => c il.1 il.2)
  obtain ⟨t₀, rfl⟩ := hb
  choose p hp using fun il : Fin n × Fin m => hbc il (Finset.mem_univ il)
  have hp' : ∀ i l, algebraMap _ (Localization.Away h) (p (i, l)) =
      algebraMap _ _ (h ^ t₀) * c i l := fun i l => by
    rw [hp (i, l), Algebra.smul_def]
  have hmem : ∀ k, ∃ t₁ : ℕ, h ^ t₁ * (h ^ t₀ * f k + ∑ i, pderiv i (f k) *
      ∑ l, p (i, l) * f l) ∈ RingHom.ker φ ^ 2 := by
    intro k
    have h1 : algebraMap _ (Localization.Away h)
        (h ^ t₀ * f k + ∑ i, pderiv i (f k) * ∑ l, p (i, l) * f l) ∈ locKer φ h ^ 2 := by
      have heq : algebraMap _ (Localization.Away h)
          (h ^ t₀ * f k + ∑ i, pderiv i (f k) * ∑ l, p (i, l) * f l) =
          algebraMap _ _ (h ^ t₀) * (algebraMap _ (Localization.Away h) (f k) +
            ∑ i, algebraMap _ _ (pderiv i (f k)) * ∑ l, c i l * algebraMap _ _ (f l)) := by
        simp only [map_add, map_mul, map_sum, hp', mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        ring
      rw [heq]
      exact Ideal.mul_mem_left _ _ (hc k)
    rw [locKer, ← Ideal.map_pow] at h1
    obtain ⟨_, ⟨t₁, rfl⟩, ht⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers h) _ _ _).mp h1
    exact ⟨t₁, ht⟩
  choose t₁ ht₁ using hmem
  let T₁ := ∑ k, t₁ k
  refine ⟨T₁ + t₀, Matrix.of fun i l => -(h ^ T₁ * p (i, l)), fun k => ?_⟩
  have hdvd : h ^ t₁ k ∣ h ^ T₁ := pow_dvd_pow h (Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  obtain ⟨d, hd⟩ := hdvd
  have hsum : ∑ l, (∑ i, pderiv i (f k) *
      (Matrix.of fun i l => -(h ^ T₁ * p (i, l))) i l) * f l =
      -(h ^ T₁ * ∑ i, pderiv i (f k) * ∑ l, p (i, l) * f l) := by
    simp only [Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have : h ^ (T₁ + t₀) * f k - ∑ l, (∑ i, pderiv i (f k) *
      (Matrix.of fun i l => -(h ^ T₁ * p (i, l))) i l) * f l =
      d * (h ^ t₁ k * (h ^ t₀ * f k + ∑ i, pderiv i (f k) * ∑ l, p (i, l) * f l)) := by
    rw [hsum, pow_add, hd]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (ht₁ k)

end Langlands.CommutativeAlgebra.Popescu.SymRetract
