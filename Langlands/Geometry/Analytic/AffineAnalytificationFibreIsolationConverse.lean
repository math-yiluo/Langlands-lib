import Langlands.Geometry.Analytic.AffineAnalytificationQuasiFiniteStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.CommutativeAlgebra.QuasiFiniteFibrePrimes
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.NoetherNormalization
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Fibre isolation in the affine analytification forces quasi-finiteness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology Polynomial

namespace FibreIsolationConverse

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

section Seminorm

variable {A : Type v} [CommRing A] [Algebra K A]

/-- Ultrametric root bound: if a multiplicative seminorm extending the norm of `K`
kills `b ^ n + ∑_{j < n} a_j b ^ j` with scalar coefficients of norm at most `C`, then
it takes a value at most `max 1 C` at `b`. -/
theorem map_le_max_of_root {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) (b : A) (n : ℕ)
    (a : ℕ → K) {C : ℝ} (hC : ∀ j < n, ‖a j‖ ≤ C)
    (h0 : ν (b ^ n + ∑ j ∈ Finset.range n, algebraMap K A (a j) * b ^ j) = 0) :
    ν b ≤ max 1 C := by
  by_contra hlt
  push Not at hlt
  have ht1 : 1 < ν b := lt_of_le_of_lt (le_max_left _ _) hlt
  have ht0 : 0 < ν b := zero_lt_one.trans ht1
  have hM0 : 0 ≤ max 1 C := le_max_of_le_left zero_le_one
  cases n with
  | zero => simp at h0
  | succ k =>
    set S := ∑ j ∈ Finset.range (k + 1), algebraMap K A (a j) * b ^ j with hS
    have hbound : ν S ≤ max 1 C * ν b ^ k := by
      apply SeminormComparison.map_sum_le_of_le hν _ _ (mul_nonneg hM0 (pow_nonneg ht0.le k))
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [map_mul, hν, map_pow]
      exact mul_le_mul ((hC j (Finset.mem_range.mp hj)).trans (le_max_right _ _))
        (pow_le_pow_right₀ ht1.le hjk) (pow_nonneg ht0.le _) hM0
    have hpow : ν b ^ (k + 1) ≤ max 1 C * ν b ^ k := by
      have e : b ^ (k + 1) = (b ^ (k + 1) + S) + -S := by ring
      calc ν b ^ (k + 1) = ν (b ^ (k + 1)) := (map_pow ν b _).symm
        _ = ν ((b ^ (k + 1) + S) + -S) := by rw [← e]
        _ ≤ max (ν (b ^ (k + 1) + S)) (ν (-S)) := SeminormComparison.add_le_max hν _ _
        _ ≤ max 1 C * ν b ^ k := by
          rw [h0, map_neg_eq_map]
          exact max_le (mul_nonneg hM0 (pow_nonneg ht0.le k)) hbound
    have hlt' : max 1 C * ν b ^ k < ν b ^ (k + 1) := by
      rw [pow_succ']
      exact mul_lt_mul_of_pos_right hlt (pow_pos ht0 k)
    linarith

variable [CompleteSpace K] {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The multiplicative seminorm `a ↦ |φ a|_{sp}` obtained from a `K`-algebra map into an
algebraic field extension, using the spectral norm of the extension. -/
def residueSeminorm (φ : A →ₐ[K] L) : MulRingSeminorm A where
  toFun a := spectralNorm K L (φ a)
  map_zero' := by simp [spectralNorm_zero]
  add_le' a b := by
    rw [map_add]
    exact map_add_le_add (spectralMulAlgNorm K L) _ _
  neg' a := by
    rw [map_neg]
    exact map_neg_eq_map (spectralMulAlgNorm K L) _
  map_one' := by
    rw [map_one]
    exact spectralNorm_one
  map_mul' a b := by
    rw [map_mul]
    exact map_mul (spectralMulAlgNorm K L) _ _

theorem residueSeminorm_apply (φ : A →ₐ[K] L) (a : A) :
    residueSeminorm φ a = spectralNorm K L (φ a) :=
  rfl

theorem extendsNorm_residueSeminorm (φ : A →ₐ[K] L) : ExtendsNorm K (residueSeminorm φ) := by
  intro c
  rw [residueSeminorm_apply, φ.commutes]
  exact spectralNorm_extends c

theorem residueSeminorm_eq_zero_iff (φ : A →ₐ[K] L) (a : A) :
    residueSeminorm φ a = 0 ↔ φ a = 0 := by
  rw [residueSeminorm_apply]
  exact map_eq_zero_iff_eq_zero (spectralMulAlgNorm K L)

end Seminorm

section Minpoly

variable {A : Type v} [CommRing A] [Algebra K A]

omit [IsUltrametricDist K] in
/-- A `K`-algebra map into a field that kills a maximal ideal `m` gives every element the
same minimal polynomial as its residue class in `A ⧸ m`. -/
theorem minpoly_eq_quotient {L : Type*} [Field L] [Algebra K L] (m : Ideal A) [m.IsMaximal]
    (ψ : A →ₐ[K] L) (h : m ≤ RingHom.ker ψ) (a : A) :
    letI := Ideal.Quotient.field m
    minpoly K (ψ a) = minpoly K (Ideal.Quotient.mk m a) := by
  let _ := Ideal.Quotient.field m
  let ψ' : A ⧸ m →ₐ[K] L := Ideal.Quotient.liftₐ m ψ (fun x hx => h hx)
  exact minpoly.algHom_eq ψ' ψ'.toRingHom.injective (Ideal.Quotient.mk m a)

omit [IsUltrametricDist K] in
/-- Two `K`-algebra maps into fields that kill the same maximal ideal give equal minimal
polynomials. -/
theorem minpoly_eq_of_le_ker {L₁ : Type*} {L₂ : Type*} [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (m : Ideal A) [m.IsMaximal] (ψ₁ : A →ₐ[K] L₁) (ψ₂ : A →ₐ[K] L₂)
    (h₁ : m ≤ RingHom.ker ψ₁) (h₂ : m ≤ RingHom.ker ψ₂) (a : A) :
    minpoly K (ψ₁ a) = minpoly K (ψ₂ a) := by
  rw [minpoly_eq_quotient m ψ₁ h₁, minpoly_eq_quotient m ψ₂ h₂]

end Minpoly

section Maximal

variable [CompleteSpace K] {B : Type w} [CommRing B] [Algebra K B] [Algebra.FiniteType K B]

variable (K) in
/-- The multiplicative seminorm of a maximal ideal `N` of a finite-type `K`-algebra: the
spectral norm of the residue field `B ⧸ N`, a finite extension of `K`. -/
def maximalSeminorm (N : Ideal B) (hN : N.IsMaximal) : MulRingSeminorm B :=
  letI := Ideal.Quotient.field N
  haveI : Module.Finite K (B ⧸ N) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ N)
  residueSeminorm (Ideal.Quotient.mkₐ K N)

theorem extendsNorm_maximalSeminorm (N : Ideal B) (hN : N.IsMaximal) :
    ExtendsNorm K (maximalSeminorm K N hN) := by
  let _ := Ideal.Quotient.field N
  have : Module.Finite K (B ⧸ N) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ N)
  exact extendsNorm_residueSeminorm (Ideal.Quotient.mkₐ K N)

theorem maximalSeminorm_eq_zero_iff (N : Ideal B) (hN : N.IsMaximal) (b : B) :
    maximalSeminorm K N hN b = 0 ↔ b ∈ N := by
  let _ := Ideal.Quotient.field N
  have : Module.Finite K (B ⧸ N) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ N)
  change residueSeminorm (Ideal.Quotient.mkₐ K N) b = 0 ↔ b ∈ N
  rw [residueSeminorm_eq_zero_iff, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

/-- Maximal ideals of `B` over the same maximal ideal of `A` induce the same seminorm on `A`. -/
theorem maximalSeminorm_comp_eq {A : Type v} [CommRing A] [Algebra K A] (f : A →ₐ[K] B)
    (m : Ideal A) [m.IsMaximal] (N N' : Ideal B) (hN : N.IsMaximal) (hN' : N'.IsMaximal)
    (hmN : m ≤ N.comap f) (hmN' : m ≤ N'.comap f) (a : A) :
    maximalSeminorm K N hN (f a) = maximalSeminorm K N' hN' (f a) := by
  let _ := Ideal.Quotient.field N
  let _ := Ideal.Quotient.field N'
  have : Module.Finite K (B ⧸ N) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ N)
  have : Module.Finite K (B ⧸ N') := finite_of_finite_type_of_isJacobsonRing K (B ⧸ N')
  change residueSeminorm (Ideal.Quotient.mkₐ K N) (f a) =
    residueSeminorm (Ideal.Quotient.mkₐ K N') (f a)
  rw [residueSeminorm_apply, residueSeminorm_apply]
  have h₁ : m ≤ RingHom.ker ((Ideal.Quotient.mkₐ K N).comp f) := fun x hx => by
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmN hx
  have h₂ : m ≤ RingHom.ker ((Ideal.Quotient.mkₐ K N').comp f) := fun x hx => by
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmN' hx
  have := minpoly_eq_of_le_ker m _ _ h₁ h₂ a
  simp only [AlgHom.comp_apply] at this
  rw [spectralNorm, spectralNorm, this]

/-- A monic scalar polynomial killed (under the seminorm of `N`) at `β` bounds the seminorm
of `β` by the maximum of `1` and a bound for its lower coefficients. -/
theorem maximalSeminorm_le_of_aeval_mem (N : Ideal B) (hN : N.IsMaximal) (β : B) (p : K[X])
    (hp : p.Monic) {C : ℝ} (hC : ∀ i < p.natDegree, ‖p.coeff i‖ ≤ C) (h : aeval β p ∈ N) :
    maximalSeminorm K N hN β ≤ max 1 C := by
  refine map_le_max_of_root (extendsNorm_maximalSeminorm N hN) β p.natDegree p.coeff hC ?_
  rw [maximalSeminorm_eq_zero_iff]
  convert h using 1
  conv_rhs => rw [hp.as_sum]
  simp [map_sum]

end Maximal

section Polynomial

omit [IsUltrametricDist K] in
/-- Evaluating at a point of the closed unit polydisc is bounded by the sum of the norms of
the coefficients. -/
theorem norm_eval_le {σ : Type*} (x : σ → K) (hx : ∀ i, ‖x i‖ ≤ 1) (a : MvPolynomial σ K) :
    ‖MvPolynomial.eval x a‖ ≤ ∑ d ∈ a.support, ‖a.coeff d‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hx i)

omit [IsUltrametricDist K] in
theorem norm_single_le {σ : Type*} [DecidableEq σ] (i₀ : σ) {c : K} (hc : ‖c‖ ≤ 1) (i : σ) :
    ‖(Pi.single i₀ c : σ → K) i‖ ≤ 1 := by
  rcases eq_or_ne i i₀ with rfl | h
  · simpa using hc
  · simp [h]

end Polynomial

section Topology

/-- In a compact set, a fibre of a continuous map to a Hausdorff space all of whose points are
isolated in the full fibre is finite. -/
theorem finite_inter_fibre_of_isolated {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (φ : X → Y) (hφ : Continuous φ) {R : Set X} (hR : IsCompact R) (x : Y)
    (h : ∀ y ∈ R ∩ φ ⁻¹' {x}, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∀ z ∈ V, φ z = φ y → z = y) :
    (R ∩ φ ⁻¹' {x}).Finite := by
  refine (hR.inter_right (isClosed_singleton.preimage hφ)).finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  obtain ⟨V, hV, hyV, hVy⟩ := h y hy
  refine ⟨V, hV, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzV, -, hz⟩
    exact hVy z hzV (hz.trans hy.2.symm)
  · rintro rfl
    exact ⟨hyV, hy⟩

end Topology

section Family

variable [CompleteSpace K] {B : Type w} [CommRing B] [Algebra K B] [Algebra.FiniteType K B]

/-- A non-maximal prime `q` of a finite-type `K`-algebra lies in a family `F c`, `c ∈ K`, of
maximal ideals separated by one element `b` (`b ≡ c` modulo `F c`), whose seminorms are
uniformly bounded on every element as `c` ranges over the closed unit ball of `K`. -/
theorem exists_maximal_family (q : Ideal B) [hqp : q.IsPrime] (hq : ¬ q.IsMaximal) :
    ∃ (b : B) (F : K → Ideal B) (hF : ∀ c, (F c).IsMaximal), (∀ c, q ≤ F c) ∧
      (∀ c, b - algebraMap K B c ∈ F c) ∧
      ∀ β : B, ∃ C : ℝ, ∀ c : K, ‖c‖ ≤ 1 → maximalSeminorm K (F c) (hF c) β ≤ C := by
  classical
  have : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hqp.ne_top
  have : Algebra.FiniteType K (B ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K q) (Ideal.Quotient.mkₐ_surjective K q)
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K (B ⧸ q)
  have hs : s ≠ 0 := by
    rintro rfl
    apply hq
    have hC : (algebraMap K (MvPolynomial (Fin 0) K)).IsIntegral :=
      RingHom.isIntegral_of_surjective _ (MvPolynomial.C_surjective (Fin 0))
    have hint := RingHom.IsIntegral.trans _ _ hC hgint
    have e : g.toRingHom.comp (algebraMap K (MvPolynomial (Fin 0) K)) =
        algebraMap K (B ⧸ q) := by
      ext x
      simp
    rw [e] at hint
    have : Algebra.IsIntegral K (B ⧸ q) := ⟨hint⟩
    have hfield : IsField (B ⧸ q) :=
      (Algebra.IsIntegral.isField_iff_isField (algebraMap K (B ⧸ q)).injective).mp
        (Field.toIsField K)
    exact Ideal.Quotient.maximal_of_isField q hfield
  let i₀ : Fin s := ⟨0, Nat.pos_of_ne_zero hs⟩
  choose b' hb' using fun i : Fin s => Ideal.Quotient.mk_surjective (I := q) (g (MvPolynomial.X i))
  let ℓ : MvPolynomial (Fin s) K →ₐ[K] B := MvPolynomial.aeval b'
  have hℓ' : (Ideal.Quotient.mkₐ K q).comp ℓ = g :=
    MvPolynomial.algHom_ext fun i => by simp [ℓ, hb']
  have hℓ : ∀ a, Ideal.Quotient.mk q (ℓ a) = g a := fun a => congrArg (fun φ => φ a) hℓ'
  let ev : K → MvPolynomial (Fin s) K →+* K := fun c => MvPolynomial.eval (Pi.single i₀ c)
  have hev_C : ∀ c x, ev c (MvPolynomial.C x) = x := fun c x => MvPolynomial.eval_C x
  have hev_max : ∀ c, (RingHom.ker (ev c)).IsMaximal := fun c =>
    RingHom.ker_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, hev_C c x⟩
  let : Algebra (MvPolynomial (Fin s) K) (B ⧸ q) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) (B ⧸ q) := ⟨hgint⟩
  have hover : ∀ c, ∃ N : Ideal (B ⧸ q), N.IsMaximal ∧
      N.comap g.toRingHom = RingHom.ker (ev c) := by
    intro c
    have := hev_max c
    obtain ⟨N, hN, hNc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B ⧸ q)
      (RingHom.ker (ev c)) (by
        intro x hx
        have hx' : g x = 0 := hx
        rw [show x = 0 from hginj (hx'.trans (map_zero g).symm)]
        exact zero_mem _)
    exact ⟨N, hN, hNc⟩
  choose N hNmax hNover using hover
  let F : K → Ideal B := fun c => (N c).comap (Ideal.Quotient.mk q)
  have hF : ∀ c, (F c).IsMaximal := fun c => by
    have := hNmax c
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hqF : ∀ c, q ≤ F c := fun c x hx => by
    change Ideal.Quotient.mk q x ∈ N c
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  have hmem : ∀ c a, ℓ a - algebraMap K B (ev c a) ∈ F c := by
    intro c a
    change Ideal.Quotient.mk q (ℓ a - algebraMap K B (ev c a)) ∈ N c
    have h1 : a - MvPolynomial.C (ev c a) ∈ RingHom.ker (ev c) := by
      rw [RingHom.mem_ker, map_sub, hev_C, sub_self]
    rw [← hNover c] at h1
    have h2 : g (a - MvPolynomial.C (ev c a)) ∈ N c := h1
    rw [map_sub, hℓ, Ideal.Quotient.mk_algebraMap]
    rwa [map_sub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes] at h2
  refine ⟨ℓ (MvPolynomial.X i₀), F, hF, hqF, fun c => ?_, fun β => ?_⟩
  · have := hmem c (MvPolynomial.X i₀)
    simpa [ev, i₀] using this
  · obtain ⟨p, hpm, hp⟩ := hgint (Ideal.Quotient.mk q β)
    let C : ℝ := ∑ i ∈ Finset.range p.natDegree, ∑ d ∈ (p.coeff i).support, ‖(p.coeff i).coeff d‖
    refine ⟨max 1 C, fun c hc => ?_⟩
    have hq' : p.eval₂ (ℓ : MvPolynomial (Fin s) K →+* B) β ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
      convert hp using 2
      exact RingHom.ext hℓ
    have hdiff : p.eval₂ (ℓ : MvPolynomial (Fin s) K →+* B) β -
        aeval β (p.map (ev c)) ∈ F c := by
      rw [aeval_def, eval₂_map, eval₂_eq_sum_range, eval₂_eq_sum_range,
        ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [← sub_mul]
      exact Ideal.mul_mem_right _ _ (hmem c _)
    refine maximalSeminorm_le_of_aeval_mem (F c) (hF c) β (p.map (ev c)) (hpm.map _) ?_ ?_
    · intro i hi
      rw [hpm.natDegree_map] at hi
      rw [Polynomial.coeff_map]
      refine (norm_eval_le _ (norm_single_le i₀ hc) _).trans ?_
      exact Finset.single_le_sum (f := fun i => ∑ d ∈ (p.coeff i).support, ‖(p.coeff i).coeff d‖)
        (fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hi)
    · have := Ideal.sub_mem _ (hqF c hq') hdiff
      rwa [sub_sub_cancel] at this

end Family

section Main

variable [CompleteSpace K] {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B]
  [Algebra K B]

open SeminormComparison AnalyticAffineSpace in
/-- If every point of the affine analytification of `B` is isolated in its fibre over the
analytification of `A`, then `f` is quasi-finite. -/
theorem quasiFinite_of_forall_isolated (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (h : ∀ y : Space K Q, ∃ V : Set (Space K Q), IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, baseMap K P Q f z = baseMap K P Q f y → z = y) :
    f.toRingHom.QuasiFinite := by
  classical
  have : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  by_contra hQF
  obtain ⟨q, hqp, hqm, hcm⟩ :=
    CommutativeAlgebra.QuasiFiniteFibrePrimes.exists_isPrime_not_isMaximal_of_not_quasiFinite f hQF
  obtain ⟨b, F, hF, hqF, hb, hbound⟩ := exists_maximal_family (K := K) q hqm
  choose C hC using fun j : Fin Q.arity => hbound (Q.map (MvPolynomial.X j))
  obtain ⟨M, hM⟩ := exists_radius_gt K (∑ j, max 1 (C j))
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  let c : ℕ → K := fun n => ϖ ^ n
  have hc : ∀ n, ‖c n‖ ≤ 1 := fun n => by
    simp only [c, norm_pow]
    exact pow_le_one₀ hϖ0.le hϖ1.le
  let ν : ℕ → MulRingSeminorm B := fun n => maximalSeminorm K (F (c n)) (hF (c n))
  have hν : ∀ n, ExtendsNorm K (ν n) := fun n => extendsNorm_maximalSeminorm _ _
  have hR : ∀ n j, ν n (Q.map (MvPolynomial.X j)) ≤ radius K M := fun n j =>
    ((hC j (c n) (hc n)).trans (le_max_right 1 (C j))).trans
      ((Finset.single_le_sum (f := fun j => max 1 (C j))
        (fun i _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ j)).trans hM.le)
  let y : ℕ → Space K Q := fun n => chart K Q M (chartPoint (hν n) (hR n))
  have hy : ∀ n, pointSeminorm K Q (y n) = ν n := fun n => by
    simp only [y, pointSeminorm_chart, chartSeminorm_chartPoint]
  have hyinj : Function.Injective y := by
    intro n m hnm
    have e : ν n = ν m := by rw [← hy, ← hy, hnm]
    have h1 : b - algebraMap K B (c n) ∈ F (c m) := by
      rw [← maximalSeminorm_eq_zero_iff (K := K) (F (c m)) (hF (c m))]
      change ν m _ = 0
      rw [← e]
      exact (maximalSeminorm_eq_zero_iff _ _ _).mpr (hb (c n))
    have h2 : algebraMap K B (c m - c n) ∈ F (c m) := by
      have := Ideal.sub_mem _ h1 (hb (c m))
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    have h3 : c m - c n = 0 := by
      by_contra hne
      exact (hF (c m)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h2 ((isUnit_iff_ne_zero.mpr hne).map _))
    have h4 : ‖ϖ‖ ^ m = ‖ϖ‖ ^ n := by
      rw [← norm_pow, ← norm_pow]
      exact congrArg norm (sub_eq_zero.mp h3)
    exact (pow_right_injective₀ hϖ0 hϖ1.ne h4).symm
  have hbase : ∀ n, baseMap K P Q f (y n) = baseMap K P Q f (y 0) := by
    intro n
    apply pointSeminorm_injective K P
    ext a
    rw [pointSeminorm_baseMap, pointSeminorm_baseMap, hy, hy]
    exact maximalSeminorm_comp_eq f (q.comap f) _ _ _ _ (Ideal.comap_mono (hqF _))
      (Ideal.comap_mono (hqF _)) a
  have hfin := finite_inter_fibre_of_isolated (baseMap K P Q f) (baseMap K P Q f).continuous
    (isCompact_range (continuous_chart K Q M)) (baseMap K P Q f (y 0)) (fun z _ => h z)
  refine Set.infinite_of_injective_forall_mem hyinj (fun n => ?_) hfin
  exact ⟨⟨_, rfl⟩, hbase n⟩

end Main

end FibreIsolationConverse

end Langlands.Analytic.AffineAnalytification
