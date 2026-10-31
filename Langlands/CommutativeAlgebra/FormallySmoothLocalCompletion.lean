import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic

/-! # Completions of formally smooth local algebras -/

namespace Langlands.CommutativeAlgebra

namespace FormallySmoothLocalCompletion

section Approximation

variable {A : Type*} [CommRing A] (I : Ideal A) (S : Subring A)
  (h0 : ∀ a, ∃ s ∈ S, a - s ∈ I) (h1 : ∀ a ∈ I, ∃ s ∈ S, s ∈ I ∧ a - s ∈ I ^ 2)
include h0 h1

/-- Graded approximation: an element of `I ^ d` agrees with an element of `S ∩ I ^ d`
modulo `I ^ (d + 1)`. -/
theorem exists_mem_sub_mem_pow_succ :
    ∀ d : ℕ, ∀ a ∈ I ^ d, ∃ s ∈ S, s ∈ I ^ d ∧ a - s ∈ I ^ (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro a _
    obtain ⟨s, hs, has⟩ := h0 a
    exact ⟨s, hs, by simp, by simpa using has⟩
  | succ d ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      obtain ⟨s, hs, hsd, hxs⟩ := ih x hx
      obtain ⟨s', hs', hs'I, hys'⟩ := h1 y hy
      refine ⟨s * s', S.mul_mem hs hs', ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hsd hs'I
      · have e : x * y - s * s' = (x - s) * y + s * (y - s') := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [pow_succ I (d + 1)]
          exact Ideal.mul_mem_mul hxs hy
        · rw [show d + 1 + 1 = d + 2 by omega, pow_add]
          exact Ideal.mul_mem_mul hsd hys'
    · rintro x y ⟨s, hs, hsd, hxs⟩ ⟨t, ht, htd, hyt⟩
      refine ⟨s + t, S.add_mem hs ht, Ideal.add_mem _ hsd htd, ?_⟩
      have e : x + y - (s + t) = (x - s) + (y - t) := by ring
      rw [e]
      exact Ideal.add_mem _ hxs hyt

/-- Every element of `A` agrees with an element of `S` modulo every power of `I`. -/
theorem exists_sub_mem_pow : ∀ d : ℕ, ∀ a, ∃ s ∈ S, a - s ∈ I ^ d := by
  intro d
  induction d with
  | zero => exact fun a ↦ ⟨0, S.zero_mem, by simp⟩
  | succ d ih =>
    intro a
    obtain ⟨s, hs, has⟩ := ih a
    obtain ⟨t, ht, -, hast⟩ := exists_mem_sub_mem_pow_succ I S h0 h1 d _ has
    exact ⟨s + t, S.add_mem hs ht, by rwa [← sub_sub]⟩

/-- If `I` is nilpotent, `S` is everything. -/
theorem mem_of_isNilpotent {N : ℕ} (hN : I ^ N = ⊥) (a : A) : a ∈ S := by
  obtain ⟨s, hs, has⟩ := exists_sub_mem_pow I S h0 h1 N a
  rw [hN, Ideal.mem_bot, sub_eq_zero] at has
  exact has ▸ hs

end Approximation

/-- A surjective ring endomorphism of a Noetherian ring is injective. -/
theorem injective_of_surjective_endo {A : Type*} [CommRing A] [IsNoetherianRing A]
    (f : A →+* A) (hf : Function.Surjective f) : Function.Injective f := by
  have hmono : Monotone fun n : ℕ ↦ RingHom.ker (f ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx ↦ ?_
    rw [RingHom.mem_ker] at hx ⊢
    rw [RingHom.coe_pow] at hx ⊢
    rw [Function.iterate_succ_apply', hx, map_zero]
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A A)
    ⟨_, hmono⟩
  refine (injective_iff_map_eq_zero f).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := hf.iterate N x
  have hy : y ∈ RingHom.ker (f ^ (N + 1)) := by
    rw [RingHom.mem_ker, RingHom.coe_pow, Function.iterate_succ_apply', hx]
  have := hN (N + 1) N.le_succ
  simp only [OrderHom.coe_mk] at this
  rw [← this, RingHom.mem_ker, RingHom.coe_pow] at hy
  exact hy

section MvPolynomial

open MvPolynomial

variable {σ K : Type*} [CommRing K]

theorem sub_C_coeff_zero_mem_idealOfVars (p : MvPolynomial σ K) :
    p - C (p.coeff 0) ∈ idealOfVars σ K := by
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  intro x hx
  have : x = 0 := by
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
    exact hx
  subst this
  simp

theorem exists_sub_sum_mem_idealOfVars_sq [Fintype σ] (p : MvPolynomial σ K)
    (hp : p ∈ idealOfVars σ K) :
    ∃ a : σ → K, p - ∑ i, C (a i) * X i ∈ idealOfVars σ K ^ 2 := by
  obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hp
  refine ⟨fun i ↦ (g i).coeff 0, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [smul_eq_mul, ← sub_mul, pow_two]
  exact Ideal.mul_mem_mul (sub_C_coeff_zero_mem_idealOfVars _)
    (Ideal.subset_span ⟨i, rfl⟩)

end MvPolynomial

section Levelwise

open IsLocalRing MvPolynomial

variable {K R : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  {n : ℕ} (t : Fin n → R) (htm : ∀ i, t i ∈ maximalIdeal R)

theorem algebraMap_mem_maximalIdeal_iff (c : K) :
    algebraMap K R c ∈ maximalIdeal R ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hc
  exact (mem_maximalIdeal _).1 h ((isUnit_iff_ne_zero.2 hc).map _)

theorem exists_sub_algebraMap_mem
    (hK : Function.Surjective (algebraMap K (ResidueField R))) (r : R) :
    ∃ c : K, r - algebraMap K R c ∈ maximalIdeal R := by
  obtain ⟨c, hc⟩ := hK (residue R r)
  refine ⟨c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hc, IsScalarTower.algebraMap_apply K R (ResidueField R),
    ResidueField.algebraMap_eq, sub_self]

include htm

theorem idealOfVars_le_comap :
    idealOfVars (Fin n) K ≤ (maximalIdeal R).comap (aeval t) := by
  rw [idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using htm i

theorem pow_idealOfVars_le_comap (k : ℕ) :
    idealOfVars (Fin n) K ^ k ≤ (maximalIdeal R ^ k).comap (aeval t) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (idealOfVars_le_comap t htm)) k

theorem mem_idealOfVars_of_aeval_mem (p : MvPolynomial (Fin n) K)
    (hp : aeval t p ∈ maximalIdeal R) : p ∈ idealOfVars (Fin n) K := by
  have h1 := sub_C_coeff_zero_mem_idealOfVars p
  have h2 : aeval t (p - C (p.coeff 0)) ∈ maximalIdeal R := idealOfVars_le_comap t htm h1
  have h3 : algebraMap K R (p.coeff 0) ∈ maximalIdeal R := by
    have := sub_mem hp h2
    simpa [map_sub, aeval_C] using this
  rw [algebraMap_mem_maximalIdeal_iff] at h3
  simpa [h3] using h1

variable (hind : ∀ a : Fin n → K,
  ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2 → a = 0)
include hind

theorem mem_idealOfVars_sq_of_aeval_mem (p : MvPolynomial (Fin n) K)
    (hp : aeval t p ∈ maximalIdeal R ^ 2) : p ∈ idealOfVars (Fin n) K ^ 2 := by
  have hpJ := mem_idealOfVars_of_aeval_mem t htm p (Ideal.pow_le_self two_ne_zero hp)
  obtain ⟨a, ha⟩ := exists_sub_sum_mem_idealOfVars_sq p hpJ
  have h2 := pow_idealOfVars_le_comap t htm 2 ha
  rw [Ideal.mem_comap] at h2
  have h3 : ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2 := by
    have := sub_mem hp h2
    simpa [map_sub, map_sum, Algebra.smul_def] using this
  obtain rfl := hind a h3
  simpa using ha

omit hind in
theorem exists_sub_aeval_mem_pow
    (hK : Function.Surjective (algebraMap K (ResidueField R)))
    (hspan : ∀ r ∈ maximalIdeal R, ∃ a : Fin n → K,
      r - ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2)
    (k : ℕ) (r : R) : ∃ p : MvPolynomial (Fin n) K, r - aeval t p ∈ maximalIdeal R ^ k := by
  have h0 : ∀ r : R, ∃ s ∈ (aeval (R := K) t).range.toSubring, r - s ∈ maximalIdeal R := by
    intro r
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem hK r
    exact ⟨_, ⟨C c, aeval_C _ _⟩, hc⟩
  have h1 : ∀ r ∈ maximalIdeal R, ∃ s ∈ (aeval (R := K) t).range.toSubring,
      s ∈ maximalIdeal R ∧ r - s ∈ maximalIdeal R ^ 2 := by
    intro r hr
    obtain ⟨a, ha⟩ := hspan r hr
    refine ⟨_, ⟨∑ i, C (a i) * X i, by simp⟩, ?_, ha⟩
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (htm i)
  obtain ⟨s, hs, hrs⟩ := exists_sub_mem_pow (maximalIdeal R) _ h0 h1 k r
  rw [Subalgebra.mem_toSubring, AlgHom.mem_range] at hs
  obtain ⟨p, rfl⟩ := hs
  exact ⟨p, hrs⟩

theorem mem_pow_idealOfVars_of_aeval_mem_pow [Algebra.FormallySmooth K R]
    (hK : Function.Surjective (algebraMap K (ResidueField R)))
    (hspan : ∀ r ∈ maximalIdeal R, ∃ a : Fin n → K,
      r - ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2)
    (k : ℕ) (p : MvPolynomial (Fin n) K) (hp : aeval t p ∈ maximalIdeal R ^ k) :
    p ∈ idealOfVars (Fin n) K ^ k := by
  obtain _ | _ | k := k
  · simp
  · rw [pow_one] at hp ⊢
    exact mem_idealOfVars_of_aeval_mem t htm p hp
  set J := idealOfVars (Fin n) K with hJ
  set m := maximalIdeal R with hm
  -- the isomorphism at level two
  let ι2 : (MvPolynomial (Fin n) K ⧸ J ^ 2) →ₐ[K] R ⧸ m ^ 2 :=
    Ideal.quotientMapₐ _ (aeval t) (pow_idealOfVars_le_comap t htm 2)
  have hι2 : Function.Bijective ι2 := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem]
      refine mem_idealOfVars_sq_of_aeval_mem t htm hind q ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    · intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨q, hq⟩ := exists_sub_aeval_mem_pow t htm hK hspan 2 r
      exact ⟨Ideal.Quotient.mk _ q, (Ideal.Quotient.eq.2 hq).symm⟩
  let e2 := AlgEquiv.ofBijective ι2 hι2
  have hle : J ^ (k + 2) ≤ J ^ 2 := Ideal.pow_le_pow_right (by omega)
  let I2 : Ideal (MvPolynomial (Fin n) K ⧸ J ^ (k + 2)) :=
    (J ^ 2).map (Ideal.Quotient.mkₐ K (J ^ (k + 2)))
  have hI2 : IsNilpotent I2 := by
    refine ⟨k + 2, ?_⟩
    rw [← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right (by omega) hx
  let g : R →ₐ[K] (MvPolynomial (Fin n) K ⧸ J ^ (k + 2)) ⧸ I2 :=
    (DoubleQuot.quotQuotEquivQuotOfLEₐ K hle).symm.toAlgHom.comp
      (e2.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K (m ^ 2)))
  let ψ : R →ₐ[K] MvPolynomial (Fin n) K ⧸ J ^ (k + 2) := Algebra.FormallySmooth.lift I2 hI2 g
  have hF : ∀ r q, ψ r = Ideal.Quotient.mk _ q → aeval t q - r ∈ m ^ 2 := by
    intro r q h
    have h1 : Ideal.Quotient.mk I2 (ψ r) = g r := Algebra.FormallySmooth.mk_lift I2 hI2 g r
    rw [h] at h1
    have h2 : DoubleQuot.quotQuotEquivQuotOfLEₐ K hle (Ideal.Quotient.mk I2
        (Ideal.Quotient.mk _ q)) = Ideal.Quotient.mk (J ^ 2) q := rfl
    have h3 : e2.symm (Ideal.Quotient.mk (m ^ 2) r) = Ideal.Quotient.mk (J ^ 2) q := by
      rw [← h2, h1]
      exact ((DoubleQuot.quotQuotEquivQuotOfLEₐ K hle).apply_symm_apply _).symm
    rw [AlgEquiv.symm_apply_eq] at h3
    have h4 : e2 (Ideal.Quotient.mk (J ^ 2) q) = Ideal.Quotient.mk (m ^ 2) (aeval t q) := rfl
    rw [h4] at h3
    exact Ideal.Quotient.eq.1 h3.symm
  set IB := J.map (Ideal.Quotient.mk (J ^ (k + 2))) with hIB
  -- `ψ` sends `m` into `IB`, hence kills `m ^ (k + 2)`
  have hψm : ∀ r ∈ m, ψ r ∈ IB := by
    intro r hr
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (ψ r)
    have h1 := hF r q hq.symm
    have h2 : aeval t q ∈ m := by
      have := add_mem (Ideal.pow_le_self two_ne_zero h1) hr
      rwa [sub_add_cancel] at this
    rw [← hq]
    exact Ideal.mem_map_of_mem _ (mem_idealOfVars_of_aeval_mem t htm q h2)
  have hN : IB ^ (k + 2) = ⊥ := by rw [hIB, ← Ideal.map_pow, Ideal.map_quotient_self]
  have hψ0 : ∀ r ∈ m ^ (k + 2), ψ r = 0 := by
    intro r hr
    have hle' : Ideal.map ψ (m ^ (k + 2)) ≤ ⊥ := by
      rw [Ideal.map_pow, ← hN]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψm) _
    exact (Ideal.mem_bot).1 (hle' (Ideal.mem_map_of_mem ψ hr))
  let ψbar : R ⧸ m ^ (k + 2) →ₐ[K] MvPolynomial (Fin n) K ⧸ J ^ (k + 2) :=
    Ideal.Quotient.liftₐ (m ^ (k + 2)) ψ hψ0
  let ιk : MvPolynomial (Fin n) K ⧸ J ^ (k + 2) →ₐ[K] R ⧸ m ^ (k + 2) :=
    Ideal.quotientMapₐ _ (aeval t) (pow_idealOfVars_le_comap t htm (k + 2))
  let θ := ψbar.comp ιk
  have hθ : ∀ q, θ (Ideal.Quotient.mk _ q) = ψ (aeval t q) := fun q ↦ rfl
  -- `θ` is surjective by the approximation lemma
  have h0' : ∀ b, ∃ s ∈ θ.range.toSubring, b - s ∈ IB := by
    intro b
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨algebraMap K _ (q.coeff 0), θ.range.algebraMap_mem _, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, ← map_sub, MvPolynomial.algebraMap_eq]
    exact Ideal.mem_map_of_mem _ (sub_C_coeff_zero_mem_idealOfVars q)
  have h1' : ∀ b ∈ IB, ∃ s ∈ θ.range.toSubring, s ∈ IB ∧ b - s ∈ IB ^ 2 := by
    intro b hb
    obtain ⟨p, hpJ, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hb
    obtain ⟨a, ha⟩ := exists_sub_sum_mem_idealOfVars_sq p hpJ
    set q : MvPolynomial (Fin n) K := ∑ i, C (a i) * X i with hq
    have hqJ : q ∈ J :=
      Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective (ψ (aeval t q))
    have h2 : p' - q ∈ J ^ 2 := by
      refine mem_idealOfVars_sq_of_aeval_mem t htm hind _ ?_
      rw [map_sub]
      exact hF _ _ hp'.symm
    have hp'J : p' ∈ J := by
      have := add_mem (Ideal.pow_le_self two_ne_zero h2) hqJ
      rwa [sub_add_cancel] at this
    refine ⟨Ideal.Quotient.mk _ p', ⟨Ideal.Quotient.mk _ q, (hθ q).trans hp'.symm⟩,
      Ideal.mem_map_of_mem _ hp'J, ?_⟩
    rw [← map_sub, hIB, ← Ideal.map_pow]
    have : p - p' = (p - q) - (p' - q) := by ring
    rw [this]
    exact Ideal.mem_map_of_mem _ (sub_mem ha h2)
  have hθsurj : Function.Surjective θ := by
    intro b
    have := mem_of_isNilpotent IB θ.range.toSubring h0' h1' hN b
    rw [Subalgebra.mem_toSubring, AlgHom.mem_range] at this
    exact this
  have hθinj : Function.Injective θ := injective_of_surjective_endo θ.toRingHom hθsurj
  have hιk : Function.Injective ιk := Function.Injective.of_comp (f := ⇑ψbar) hθinj
  show p ∈ J ^ (k + 2)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine hιk ?_
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hp

end Levelwise

section Completion

open AdicCompletion

theorem factor_evalₐ {A : Type*} [CommRing A] (I : Ideal A) {a b : ℕ} (hab : a ≤ b)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (evalₐ I b x) = evalₐ I a x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hab]

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  (I : Ideal A) (J : Ideal B) (e : ∀ k : ℕ, (A ⧸ I ^ k) ≃ₐ[K] B ⧸ J ^ k)
  (he : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (e b x) =
      e a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x))

include he in
theorem factor_symm {a b : ℕ} (hab : a ≤ b) (y : B ⧸ J ^ b) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) ((e b).symm y) =
      (e a).symm (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) y) := by
  rw [AlgEquiv.eq_symm_apply, ← he hab, AlgEquiv.apply_symm_apply]

/-- Compatible isomorphisms of the truncations induce an isomorphism of adic completions. -/
noncomputable def adicCompletionAlgEquiv : AdicCompletion I A ≃ₐ[K] AdicCompletion J B :=
  AlgEquiv.ofAlgHom
    (liftAlgHom J (fun k ↦ (e k).toAlgHom.comp ((evalₐ I k).restrictScalars K))
      fun hle ↦ AlgHom.ext fun x ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.factorₐ_apply]
        exact (he hle _).trans (congrArg (e _) (factor_evalₐ I hle x)))
    (liftAlgHom I (fun k ↦ (e k).symm.toAlgHom.comp ((evalₐ J k).restrictScalars K))
      fun hle ↦ AlgHom.ext fun x ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.factorₐ_apply]
        exact (factor_symm I J e he hle _).trans (congrArg (e _).symm (factor_evalₐ J hle x)))
    (AlgHom.ext fun x ↦ ext_evalₐ fun k ↦ by simp)
    (AlgHom.ext fun x ↦ ext_evalₐ fun k ↦ by simp)

end Completion

section Main

open IsLocalRing MvPolynomial

variable {K R : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [Algebra.FormallySmooth K R] {n : ℕ} (t : Fin n → R) (htm : ∀ i, t i ∈ maximalIdeal R)
  (hind : ∀ a : Fin n → K, ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2 → a = 0)
  (hK : Function.Surjective (algebraMap K (ResidueField R)))
  (hspan : ∀ r ∈ maximalIdeal R, ∃ a : Fin n → K,
    r - ∑ i, algebraMap K R (a i) * t i ∈ maximalIdeal R ^ 2)
include htm hind hK hspan

/-- The truncation isomorphisms `K[T₁, …, Tₙ] ⧸ J ^ k ≃ R ⧸ m ^ k` sending `Tᵢ` to `tᵢ`. -/
noncomputable def truncEquiv (k : ℕ) :
    (MvPolynomial (Fin n) K ⧸ idealOfVars (Fin n) K ^ k) ≃ₐ[K] R ⧸ maximalIdeal R ^ k :=
  AlgEquiv.ofBijective (Ideal.quotientMapₐ _ (aeval t) (pow_idealOfVars_le_comap t htm k)) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem]
      refine mem_pow_idealOfVars_of_aeval_mem_pow t htm hind hK hspan k q ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨q, hq⟩ := exists_sub_aeval_mem_pow t htm hK hspan k r
      exact ⟨Ideal.Quotient.mk _ q, (Ideal.Quotient.eq.2 hq).symm⟩

theorem truncEquiv_mk (k : ℕ) (q : MvPolynomial (Fin n) K) :
    truncEquiv t htm hind hK hspan k (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (aeval t q) :=
  rfl

theorem factor_truncEquiv {a b : ℕ} (hab : a ≤ b)
    (x : MvPolynomial (Fin n) K ⧸ idealOfVars (Fin n) K ^ b) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (truncEquiv t htm hind hK hspan b x) =
      truncEquiv t htm hind hK hspan a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The completion of `R` is isomorphic to the power series ring `K⟦T₁, …, Tₙ⟧`. -/
noncomputable def completionEquiv :
    AdicCompletion (maximalIdeal R) R ≃ₐ[K] MvPowerSeries (Fin n) K :=
  (adicCompletionAlgEquiv (idealOfVars (Fin n) K) (maximalIdeal R)
    (truncEquiv t htm hind hK hspan) (factor_truncEquiv t htm hind hK hspan)).symm.trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) K).restrictScalars K).symm

end Main

open IsLocalRing in
/-- **Completion of a formally smooth local algebra.** If `R` is a Noetherian local ring that
is formally smooth over a field `K` mapping onto its residue field, then the
`maximalIdeal R`-adic completion of `R` is `K`-isomorphic to a power series ring over `K` in
finitely many variables. -/
theorem exists_algEquiv_mvPowerSeries {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra K R] [Algebra.FormallySmooth K R]
    (hK : Function.Surjective (algebraMap K (ResidueField R))) :
    ∃ n : ℕ, Nonempty (AdicCompletion (maximalIdeal R) R ≃ₐ[K] MvPowerSeries (Fin n) K) := by
  set m := maximalIdeal R
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose t' ht' using fun i ↦ m.toCotangent_surjective (b i)
  let t : Fin _ → R := fun i ↦ t' i
  have htm : ∀ i, t i ∈ m := fun i ↦ (t' i).2
  have key : ∀ a : Fin _ → K, m.toCotangent (∑ i, algebraMap K R (a i) • t' i) =
      ∑ i, algebraMap K (ResidueField R) (a i) • b i := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ht', ← algebraMap_smul (ResidueField R) (algebraMap K R (a i)) (b i),
      ← IsScalarTower.algebraMap_apply]
  have hcoe : ∀ a : Fin _ → K,
      ((∑ i, algebraMap K R (a i) • t' i : m) : R) = ∑ i, algebraMap K R (a i) * t i := by
    intro a
    simp [t, Algebra.smul_def]
  refine ⟨_, ⟨completionEquiv t htm ?_ hK ?_⟩⟩
  · intro a ha
    rw [← hcoe, ← Ideal.toCotangent_eq_zero, key] at ha
    funext i
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ ha i
    simpa using this
  · intro r hr
    choose a ha using fun i ↦ hK (b.repr (m.toCotangent ⟨r, hr⟩) i)
    refine ⟨a, ?_⟩
    rw [← hcoe]
    change ((⟨r, hr⟩ : m) : R) - _ ∈ _
    rw [← Ideal.toCotangent_eq, key]
    simp_rw [ha]
    exact (b.sum_repr _).symm

end FormallySmoothLocalCompletion

end Langlands.CommutativeAlgebra
