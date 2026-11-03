import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Unipotent algebra maps out of truncated polynomial rings -/

noncomputable section

namespace Langlands.GroupScheme.TorusUnipotence

open MvPolynomial

section General

variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R] [Algebra k B] [Algebra k R]

/-- Two algebra maps sending an ideal `𝔪` with `B = k + 𝔪` into `J` agree modulo `J`. -/
theorem sub_mem_of_map_le (𝔪 : Ideal B) (hB : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ 𝔪)
    (J : Ideal R) (e f : B →ₐ[k] R) (he : 𝔪.map e ≤ J) (hf : 𝔪.map f ≤ J) (p : B) :
    e p - f p ∈ J := by
  obtain ⟨c, hc⟩ := hB p
  have h1 : e (p - algebraMap k B c) ∈ J := he (Ideal.mem_map_of_mem _ hc)
  have h2 : f (p - algebraMap k B c) ∈ J := hf (Ideal.mem_map_of_mem _ hc)
  have : e p - f p = e (p - algebraMap k B c) - f (p - algebraMap k B c) := by
    simp only [map_sub, AlgHom.commutes, sub_sub_sub_cancel_right]
  rw [this]
  exact J.sub_mem h1 h2

/-- If two algebra maps agree modulo `J ^ 2` on generators of `𝔪`, they agree modulo
`J ^ 2` on `𝔪`. -/
theorem sub_mem_sq_of_mem (𝔪 : Ideal B) (S : Set B) (hS : Ideal.span S = 𝔪)
    (hB : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ 𝔪)
    (J : Ideal R) (e f : B →ₐ[k] R) (he : 𝔪.map e ≤ J) (hf : 𝔪.map f ≤ J)
    (hgen : ∀ s ∈ S, e s - f s ∈ J ^ 2) {p : B} (hp : p ∈ 𝔪) : e p - f p ∈ J ^ 2 := by
  rw [← hS] at hp
  induction hp using Submodule.span_induction with
  | mem s hs => exact hgen s hs
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hx hy
  | smul r x hx ihx =>
    have hx' : x ∈ 𝔪 := hS ▸ hx
    rw [smul_eq_mul, map_mul, map_mul]
    have : e r * e x - f r * f x = e r * (e x - f x) + (e r - f r) * f x := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ihx) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (sub_mem_of_map_le 𝔪 hB J e f he hf r)
      (hf (Ideal.mem_map_of_mem _ hx'))

/-- If two algebra maps agree modulo `J ^ 2` on generators of `𝔪` and send `𝔪` into `J`,
they agree modulo `J ^ (m + 1)` on `𝔪 ^ m`. -/
theorem sub_mem_pow_succ (𝔪 : Ideal B) (S : Set B) (hS : Ideal.span S = 𝔪)
    (hB : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ 𝔪)
    (J : Ideal R) (e f : B →ₐ[k] R) (he : 𝔪.map e ≤ J) (hf : 𝔪.map f ≤ J)
    (hgen : ∀ s ∈ S, e s - f s ∈ J ^ 2) :
    ∀ (m : ℕ) {p : B}, p ∈ 𝔪 ^ m → e p - f p ∈ J ^ (m + 1) := by
  have hsucc : ∀ (m : ℕ) {p : B}, p ∈ 𝔪 ^ (m + 1) → e p - f p ∈ J ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      exact sub_mem_sq_of_mem 𝔪 S hS hB J e f he hf hgen (by simpa using hp)
    | succ m ih =>
      intro p hp
      rw [pow_succ] at hp
      refine Submodule.mul_induction_on hp ?_ ?_
      · intro a ha b hb
        rw [map_mul, map_mul]
        have : e a * e b - f a * f b = e a * (e b - f b) + (e a - f a) * f b := by ring
        rw [this]
        refine Ideal.add_mem _ ?_ ?_
        · have h1 : e a ∈ J ^ (m + 1) := by
            have : e a ∈ (𝔪 ^ (m + 1)).map e := Ideal.mem_map_of_mem _ ha
            rw [Ideal.map_pow] at this
            exact Ideal.pow_right_mono he _ this
          have h2 := sub_mem_sq_of_mem 𝔪 S hS hB J e f he hf hgen hb
          have := Ideal.mul_mem_mul h1 h2
          rwa [← pow_add] at this
        · have h1 := ih ha
          have h2 : f b ∈ J := hf (Ideal.mem_map_of_mem _ hb)
          have := Ideal.mul_mem_mul h1 h2
          rw [← pow_succ] at this
          have hmn : m + 1 + 2 = m + 2 + 1 := by omega
          rwa [hmn]
      · intro x y hx hy
        rw [map_add, map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx hy
  intro m p hp
  cases m with
  | zero => simpa using sub_mem_of_map_le 𝔪 hB J e f he hf p
  | succ m => exact hsucc m hp

/-- An algebra map `e : B → B ⧸ 𝔪 ^ N` which agrees with the quotient map modulo the square of
the image of `𝔪` on generators of `𝔪` has kernel contained in `𝔪 ^ N`. -/
theorem mem_pow_of_eq_zero_of_span (𝔪 : Ideal B) (S : Set B) (hS : Ideal.span S = 𝔪)
    (hB : ∀ b : B, ∃ c : k, b - algebraMap k B c ∈ 𝔪) {N : ℕ} (e : B →ₐ[k] B ⧸ 𝔪 ^ N)
    (he : ∀ s ∈ S, e s - Ideal.Quotient.mk (𝔪 ^ N) s ∈ (𝔪.map (Ideal.Quotient.mk (𝔪 ^ N))) ^ 2)
    {p : B} (hp : e p = 0) : p ∈ 𝔪 ^ N := by
  have hXJ : ∀ s ∈ S, Ideal.Quotient.mk (𝔪 ^ N) s ∈ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ N)) :=
    fun s hs => Ideal.mem_map_of_mem _ (hS ▸ Ideal.subset_span hs)
  have he' : 𝔪.map e ≤ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ N)) := by
    rw [Ideal.map_le_iff_le_comap]
    have : Ideal.span S ≤ (𝔪.map (Ideal.Quotient.mk (𝔪 ^ N))).comap e := by
      rw [Ideal.span_le]
      intro s hs
      have : e s = (e s - Ideal.Quotient.mk _ s) + Ideal.Quotient.mk _ s := by ring
      change e s ∈ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ N))
      rw [this]
      exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (he s hs)) (hXJ s hs)
    rwa [hS] at this
  have hf' : 𝔪.map (Ideal.Quotient.mkₐ k (𝔪 ^ N)) ≤ 𝔪.map (Ideal.Quotient.mk (𝔪 ^ N)) := by
    rw [Ideal.map_le_iff_le_comap]
    have : Ideal.span S ≤ (𝔪.map (Ideal.Quotient.mk (𝔪 ^ N))).comap
        (Ideal.Quotient.mkₐ k (𝔪 ^ N)) := Ideal.span_le.2 hXJ
    rwa [hS] at this
  have key : ∀ m, m ≤ N → p ∈ 𝔪 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h := sub_mem_pow_succ 𝔪 S hS hB _ e _ he' hf' he m (ih (by omega))
      rw [hp, zero_sub, neg_mem_iff, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.map_pow,
        Ideal.mem_quotient_iff_mem_sup] at h
      exact (sup_le le_rfl (Ideal.pow_le_pow_right hm) : 𝔪 ^ (m + 1) ⊔ 𝔪 ^ N ≤ 𝔪 ^ (m + 1)) h
  exact key N le_rfl

end General

section Polynomial

variable {k : Type*} [CommRing k] {σ : Type*}

/-- A polynomial minus its constant term lies in the ideal of the variables. -/
theorem sub_C_constantCoeff_mem_idealOfVars (p : MvPolynomial σ k) :
    p - C (constantCoeff p) ∈ idealOfVars σ k := by
  rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff']
  intro x hx
  have : x = 0 := by simpa [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using hx
  subst this
  simp [MvPolynomial.constantCoeff_eq]

/-- The ideal of the variables is the kernel of the constant coefficient. -/
theorem mem_idealOfVars_iff (p : MvPolynomial σ k) :
    p ∈ idealOfVars σ k ↔ constantCoeff p = 0 := by
  constructor
  · intro hp
    rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff'] at hp
    simpa [MvPolynomial.constantCoeff_eq] using hp 0 (by simp)
  · intro hp
    simpa [hp] using sub_C_constantCoeff_mem_idealOfVars p

/-- An algebra map from polynomials to a truncation of polynomials which is the identity on the
variables modulo the square of the variable ideal is injective on the truncation. -/
theorem mem_pow_of_eq_zero {N : ℕ}
    (e : MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N)
    (he : ∀ s, e (X s) - Ideal.Quotient.mk _ (X s) ∈
      ((idealOfVars σ k).map (Ideal.Quotient.mk (idealOfVars σ k ^ N))) ^ 2)
    {p : MvPolynomial σ k} (hp : e p = 0) : p ∈ idealOfVars σ k ^ N :=
  mem_pow_of_eq_zero_of_span (idealOfVars σ k) (Set.range X) rfl
    (fun b => ⟨constantCoeff b, sub_C_constantCoeff_mem_idealOfVars b⟩) e
    (by rintro _ ⟨s, rfl⟩; exact he s) hp

end Polynomial

end Langlands.GroupScheme.TorusUnipotence
