import Langlands.MathlibBase

/-! # Tools for the proof of Stacks 07F0 (desingularization along a strictly standard element) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.Desing

open MvPolynomial

section Chart

/-- A naive presentation `R[X_σ] ⧸ (v_ι)` with an injective choice `a : ι → σ` of variables becomes
standard smooth after inverting its Jacobian (times any element). -/
theorem isStandardSmooth_away_det_mul {R : Type u} [CommRing R] {σ ι : Type} [Fintype ι]
    [DecidableEq ι] [Finite σ] (v : ι → MvPolynomial σ R) (a : ι → σ) (ha : Function.Injective a)
    (t : MvPolynomial σ R ⧸ Ideal.span (Set.range v)) :
    Algebra.IsStandardSmooth R (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range v)) (Matrix.det fun i j : ι ↦ pderiv (a i) (v j)) * t)) := by
  classical
  let P₀ := Algebra.PreSubmersivePresentation.naive (v := v) a ha
  set d := Ideal.Quotient.mk (Ideal.span (Set.range v)) (Matrix.det fun i j : ι ↦ pderiv (a i) (v j))
    with hd
  have hP₀ : P₀.jacobian = d := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hd]
    congr 2
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  let Q := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away (d * t)) (d * t)
  have hunit : IsUnit (algebraMap _ (Localization.Away (d * t)) (d * t)) :=
    IsLocalization.Away.algebraMap_isUnit (d * t)
  have hunit' : IsUnit (algebraMap _ (Localization.Away (d * t)) d) := by
    rw [map_mul] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  let PB : Algebra.SubmersivePresentation R (Localization.Away (d * t)) (Unit ⊕ σ) (Unit ⊕ ι) :=
    { toPreSubmersivePresentation := Q.comp P₀
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def, hP₀]
        exact hunit'.mul hunit }
  exact PB.isStandardSmooth

end Chart

section Quotient

/-- If every element of the kernel of a surjection `p : A₀ → A` dies after inverting `s`, then
inverting `s` in `A₀` or `p s` in `A` gives the same algebra. -/
theorem nonempty_algEquiv_away_of_ker {R A₀ A : Type*} [CommRing R] [CommRing A₀] [CommRing A]
    [Algebra R A₀] [Algebra R A] (p : A₀ →ₐ[R] A) (hp : Function.Surjective p) (s : A₀)
    (hs : ∀ y ∈ RingHom.ker p, algebraMap A₀ (Localization.Away s) y = 0) :
    Nonempty (Localization.Away (p s) ≃ₐ[R] Localization.Away s) := by
  let φ : A →ₐ[R] Localization.Away s := AlgHom.liftOfSurjective p hp
    (IsScalarTower.toAlgHom R A₀ (Localization.Away s))
    (fun y hy ↦ (RingHom.mem_ker).mpr (hs y ((RingHom.mem_ker).mpr ((RingHom.mem_ker).mp hy))))
  have hφ : ∀ x, φ (p x) = algebraMap A₀ _ x := fun x ↦ AlgHom.liftOfSurjective_apply _ _ _ _ x
  let _ : Algebra A (Localization.Away s) := φ.toRingHom.toAlgebra
  have hφ' : ∀ x, algebraMap A (Localization.Away s) x = φ x := fun _ ↦ rfl
  have : IsScalarTower R A (Localization.Away s) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [hφ', φ.commutes]
  have : IsLocalization.Away (p s) (Localization.Away s) := by
    show IsLocalization (Submonoid.powers (p s)) (Localization.Away s)
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      rw [hφ', map_pow, hφ]
      exact (IsLocalization.Away.algebraMap_isUnit s).pow k
    · intro z
      obtain ⟨⟨x, _, k, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
      refine ⟨⟨p x, ⟨p s ^ k, k, rfl⟩⟩, ?_⟩
      simp only [hφ', ← map_pow, hφ]
      exact IsLocalization.mk'_spec _ _ _
    · intro x y hxy
      obtain ⟨x, rfl⟩ := hp x
      obtain ⟨y, rfl⟩ := hp y
      rw [hφ', hφ', hφ, hφ, IsLocalization.eq_iff_exists (Submonoid.powers s)] at hxy
      obtain ⟨⟨_, k, rfl⟩, hc⟩ := hxy
      refine ⟨⟨p s ^ k, k, rfl⟩, ?_⟩
      simp only [← map_pow, ← map_mul]
      rw [hc]
  exact ⟨(IsLocalization.algEquiv (Submonoid.powers (p s)) (Localization.Away (p s))
    (Localization.Away s)).restrictScalars R⟩

/-- Smoothness version of `nonempty_algEquiv_away_of_ker`. -/
theorem smooth_away_of_ker {R A₀ A : Type*} [CommRing R] [CommRing A₀] [CommRing A]
    [Algebra R A₀] [Algebra R A] (p : A₀ →ₐ[R] A) (hp : Function.Surjective p) (s : A₀)
    (hs : ∀ y ∈ RingHom.ker p, algebraMap A₀ (Localization.Away s) y = 0)
    [Algebra.Smooth R (Localization.Away s)] : Algebra.Smooth R (Localization.Away (p s)) := by
  obtain ⟨e⟩ := nonempty_algEquiv_away_of_ker p hp s hs
  exact Algebra.Smooth.of_equiv e.symm

end Quotient

section SmoothAt

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem isSmoothAt_of_smooth_away [Algebra.FinitePresentation R A] {s : A}
    (hs : Algebra.Smooth R (Localization.Away s)) (q : Ideal A) [q.IsPrime] (hq : s ∉ q) :
    Algebra.IsSmoothAt R q :=
  (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := R) (f := s)).mpr hs
    (show (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen s from hq)

theorem smooth_away_of_isSmoothAt [Algebra.FinitePresentation R A] {s : A}
    (h : ∀ (q : Ideal A) [q.IsPrime], s ∉ q → Algebra.IsSmoothAt R q) :
    Algebra.Smooth R (Localization.Away s) := by
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro x hx
  exact h x.asIdeal hx

end SmoothAt

section Ann

/-- In a flat module, `π² y = 0` implies `π y = 0` if this holds in the base ring. -/
theorem smul_eq_zero_of_flat {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] {π : R} (hπ : ∀ x : R, π ^ 2 * x = 0 → π * x = 0) {y : M}
    (hy : π ^ 2 • y = 0) : π • y = 0 := by
  obtain ⟨K, a, y', hy', hrel⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R)
    (M := M) (f := fun _ : Fin 1 ↦ π ^ 2) (x := fun _ ↦ y) (by simpa using hy)
  have h0 : y = ∑ j, a 0 j • y' j := hy' 0
  have ha : ∀ j, π * a 0 j = 0 := fun j ↦ hπ _ (by simpa using hrel j)
  rw [h0, Finset.smul_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [smul_smul, ha j, zero_smul]

/-- `Ann(π) = Ann(π²)` implies `Ann(π) = Ann(π^(k+1))`. -/
theorem smul_eq_zero_of_pow_smul_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {π : R} (hπ : ∀ y : M, π ^ 2 • y = 0 → π • y = 0) (k : ℕ) {y : M}
    (hy : π ^ (k + 1) • y = 0) : π • y = 0 := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    apply ih
    have h2 : π ^ 2 • (π ^ k • y) = 0 := by
      rw [← mul_smul, ← pow_add]
      rw [show k + 1 + 1 = 2 + k by omega] at hy
      exact hy
    have := hπ _ h2
    rwa [← mul_smul, ← pow_succ'] at this

end Ann

section Taylor

/-- First-order Taylor expansion: `p(a + y) ≡ p(a) + Σ ∂ᵢp(a) yᵢ` modulo `J²` when all `yᵢ ∈ J`. -/
theorem aeval_add_sub_mem {ι D S : Type*} [Fintype ι] [CommRing D] [CommRing S] [Algebra D S]
    (J : Ideal S) (a y : ι → S) (hy : ∀ i, y i ∈ J) (p : MvPolynomial ι D) :
    aeval (a + y) p - aeval a p - ∑ i, aeval a (pderiv i p) * y i ∈ J ^ 2 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C d => simp
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    convert this using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p i hp =>
    have hL : ∑ k, aeval a (pderiv k p) * y k ∈ J :=
      Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_left _ _ (hy k)
    have h1 : ∀ k, aeval a (pderiv k (p * X i)) =
        aeval a (pderiv k p) * a i + aeval a p * (if i = k then 1 else 0) := by
      intro k
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        aeval_X, Pi.single_apply]
      split_ifs with h
      · subst h; simp; ring
      · simp [mul_comm]
    have key : aeval (a + y) (p * X i) - aeval a (p * X i) -
        ∑ k, aeval a (pderiv k (p * X i)) * y k =
        (aeval (a + y) p - aeval a p - ∑ k, aeval a (pderiv k p) * y k) * (a i + y i) +
          (∑ k, aeval a (pderiv k p) * y k) * y i := by
      simp only [h1, add_mul, Finset.sum_add_distrib, map_mul, aeval_X, Pi.add_apply, mul_assoc,
        ite_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      have hs : ∑ x, aeval a (pderiv x p) * (a i * y x) = a i * ∑ k, aeval a (pderiv k p) * y k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hs]
      ring
    rw [key]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hL (hy i)

end Taylor

section Matrix

/-- Stacks, Algebra, Lemma 15.5 (one direction): if `b` is a combination of the maximal minors of a
`c × n` matrix `M`, then `M S = b • 1` for some `n × c` matrix `S`. -/
theorem exists_mul_eq_smul_one {D : Type*} [CommRing D] {c n : ℕ} (M : Matrix (Fin c) (Fin n) D)
    (b : D) (hb : b ∈ Ideal.span (Set.range fun e : Fin c ↪o Fin n ↦ (M.submatrix id e).det)) :
    ∃ S : Matrix (Fin n) (Fin c) D, M * S = b • (1 : Matrix (Fin c) (Fin c) D) := by
  classical
  obtain ⟨r, hr⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hb
  let P : (Fin c ↪o Fin n) → Matrix (Fin n) (Fin c) D :=
    fun e ↦ Matrix.of fun i k ↦ if e k = i then 1 else 0
  have hP : ∀ e, M * P e = M.submatrix id e := by
    intro e
    ext j k
    simp [P, Matrix.mul_apply]
  refine ⟨r.sum fun e x ↦ x • (P e * (M.submatrix id e).adjugate), ?_⟩
  rw [← hr, Finsupp.sum, Finsupp.sum, Matrix.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, hP, Matrix.mul_adjugate, smul_smul, smul_eq_mul]

end Matrix

section Trans

/-- Smoothness at a prime is transitive: `D → B` smooth at `q` and `R → D` smooth at `q ∩ D`. -/
theorem isSmoothAt_trans {R D B : Type*} [CommRing R] [CommRing D] [CommRing B] [Algebra R D]
    [Algebra D B] [Algebra R B] [IsScalarTower R D B] (q : Ideal B) [q.IsPrime]
    (hB : Algebra.IsSmoothAt D q) (hD : Algebra.IsSmoothAt R (q.under D)) :
    Algebra.IsSmoothAt R q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under D) q
  have : Algebra.FormallySmooth (Localization.AtPrime (q.under D)) (Localization.AtPrime q) :=
    Algebra.FormallySmooth.of_restrictScalars D _ _
  exact Algebra.FormallySmooth.comp R (Localization.AtPrime (q.under D)) (Localization.AtPrime q)

end Trans

section StrictlyStandard

/-- Stacks 07CA (first half), in a flexible form: let `K = (F₁) + (F₂)` in `D[X_ι]` and let `a` lie in
the ideal generated by `K` and the maximal minors `det (∂ F₁ j / ∂ X (μ i))` of the first block, with
`a F₂ t ∈ (F₁) + K²`. Then `D[X_ι] ⧸ K` is smooth over `D` at every prime not containing `a`. -/
theorem isSmoothAt_of_strictlyStandard {D : Type u} [CommRing D] {ι σ τ : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (F₁ : σ → MvPolynomial ι D) (F₂ : τ → MvPolynomial ι D) (K : Ideal (MvPolynomial ι D))
    (hK : K = Ideal.span (Set.range F₁) ⊔ Ideal.span (Set.range F₂)) (a : MvPolynomial ι D)
    (ha : a ∈ Ideal.span (Set.range fun μ : {μ : σ → ι // Function.Injective μ} ↦
      Matrix.det fun i j : σ ↦ pderiv (μ.1 i) (F₁ j)) ⊔ K)
    (ha₂ : ∀ t, a * F₂ t ∈ Ideal.span (Set.range F₁) ⊔ K ^ 2)
    (q : Ideal (MvPolynomial ι D ⧸ K)) [q.IsPrime] (hq : Ideal.Quotient.mk K a ∉ q) :
    Algebra.IsSmoothAt D q := by
  classical
  set K₁ := Ideal.span (Set.range F₁) with hK₁
  have hK₁K : K₁ ≤ K := hK ▸ le_sup_left
  let p : (MvPolynomial ι D ⧸ K₁) →ₐ[D] MvPolynomial ι D ⧸ K := Ideal.Quotient.factorₐ D hK₁K
  have hp : ∀ x, p (Ideal.Quotient.mk K₁ x) = Ideal.Quotient.mk K x := fun _ ↦ rfl
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hp x⟩
  let f₂ : τ → MvPolynomial ι D ⧸ K₁ := fun t ↦ Ideal.Quotient.mk K₁ (F₂ t)
  set N := Ideal.span (Set.range f₂) with hN
  have hmapK : K.map (Ideal.Quotient.mk K₁) = N := by
    rw [hK, Ideal.map_sup, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    have : Ideal.span (Set.range (⇑(Ideal.Quotient.mk K₁) ∘ F₁)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    rw [this, bot_sup_eq]
    rfl
  have hkerp : ∀ y ∈ RingHom.ker p, y ∈ N := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, hp, Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [← hmapK]
    exact Ideal.mem_map_of_mem _ hy
  -- the determinant trick
  have hY : ∀ t, ∃ y : τ → MvPolynomial ι D ⧸ K₁, (∀ t', y t' ∈ N) ∧
      Ideal.Quotient.mk K₁ a * f₂ t = ∑ t', y t' * f₂ t' := by
    intro t
    have h1 : Ideal.Quotient.mk K₁ (a * F₂ t) ∈ N • Ideal.span (Set.range f₂) := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk K₁) (ha₂ t)
      rw [Ideal.map_sup, Ideal.map_pow, hmapK] at this
      have h0 : K₁.map (Ideal.Quotient.mk K₁) = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      rwa [h0, bot_sup_eq, pow_two] at this
    obtain ⟨c, hc, hcs⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ _ _).mp h1
    refine ⟨c, hc, ?_⟩
    rw [← map_mul, ← hcs, Finsupp.sum_fintype]
    · rfl
    · intro i
      exact zero_smul _ _
  choose Y hYN hYeq using hY
  let M : Matrix τ τ (MvPolynomial ι D ⧸ K₁) :=
    Ideal.Quotient.mk K₁ a • (1 : Matrix τ τ _) - Matrix.of Y
  set s := M.det with hs
  have hMf : M.mulVec f₂ = 0 := by
    show (Ideal.Quotient.mk K₁ a • (1 : Matrix τ τ _) - Matrix.of Y).mulVec f₂ = 0
    ext t
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hYeq t, Pi.zero_apply, sub_eq_zero]
    rfl
  have hsf : ∀ t, s * f₂ t = 0 := by
    intro t
    have := congrArg (fun v ↦ (M.adjugate.mulVec v) t) hMf
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  have hsmod : Ideal.Quotient.mk N s = Ideal.Quotient.mk N (Ideal.Quotient.mk K₁ a) ^
      Fintype.card τ := by
    rw [hs, RingHom.map_det (S := (MvPolynomial ι D ⧸ K₁) ⧸ N) (Ideal.Quotient.mk N) M]
    have : (Ideal.Quotient.mk N).mapMatrix M =
        Ideal.Quotient.mk N (Ideal.Quotient.mk K₁ a) • (1 : Matrix τ τ _) := by
      ext t t'
      set_option synthInstance.maxHeartbeats 40000 in
      simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul, map_sub, map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hYN t t'), sub_zero]
      by_cases h : t = t' <;> simp [h, Matrix.one_apply]
    rw [this, Matrix.det_smul, Matrix.det_one]
    exact mul_one (Ideal.Quotient.mk N (Ideal.Quotient.mk K₁ a) ^ Fintype.card τ)
  have hps : p s = Ideal.Quotient.mk K a ^ Fintype.card τ := by
    have : s - Ideal.Quotient.mk K₁ a ^ Fintype.card τ ∈ N := by
      rw [← Ideal.Quotient.eq, hsmod, map_pow]
    rw [← hmapK] at this
    obtain ⟨z, hz, hzx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp this
    have h2 : p (s - Ideal.Quotient.mk K₁ a ^ Fintype.card τ) = 0 := by
      rw [← hzx, hp, Ideal.Quotient.eq_zero_iff_mem]
      exact hz
    rw [map_sub, sub_eq_zero, map_pow, hp] at h2
    exact h2
  -- a minor not in the prime
  let q' := q.comap (Ideal.Quotient.mk K)
  have hKq' : K ≤ q' := fun x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.zero_mem
  obtain ⟨μ, hμ⟩ : ∃ μ : {μ : σ → ι // Function.Injective μ},
      (Matrix.det fun i j : σ ↦ pderiv (μ.1 i) (F₁ j)) ∉ q' := by
    by_contra! h
    apply hq
    have : Ideal.span (Set.range fun μ : {μ : σ → ι // Function.Injective μ} ↦
        Matrix.det fun i j : σ ↦ pderiv (μ.1 i) (F₁ j)) ⊔ K ≤ q' := by
      refine sup_le ?_ hKq'
      rw [Ideal.span_le]
      rintro _ ⟨μ, rfl⟩
      exact h μ
    exact this ha
  -- the chart
  let J := Ideal.Quotient.mk K₁ (Matrix.det fun i j : σ ↦ pderiv (μ.1 i) (F₁ j))
  let s₀ := J * (s * Ideal.Quotient.mk K₁ a)
  have hstd : Algebra.IsStandardSmooth D (Localization.Away s₀) :=
    isStandardSmooth_away_det_mul F₁ μ.1 μ.2 (s * Ideal.Quotient.mk K₁ a)
  have hkill : ∀ y ∈ RingHom.ker p, algebraMap _ (Localization.Away s₀) y = 0 := by
    intro y hy
    have hyN := hkerp y hy
    have hle : N ≤ RingHom.ker (algebraMap _ (Localization.Away s₀)) := by
      rw [Ideal.span_le]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hu : IsUnit (algebraMap _ (Localization.Away s₀) s₀) :=
        IsLocalization.Away.algebraMap_isUnit s₀
      have h0 : algebraMap _ (Localization.Away s₀) (s₀ * f₂ t) = 0 := by
        rw [show s₀ * f₂ t = J * Ideal.Quotient.mk K₁ a * (s * f₂ t) by ring, hsf, mul_zero,
          map_zero]
      rw [map_mul] at h0
      exact (hu.mul_right_eq_zero).mp h0
    exact hle hyN
  have hsm : Algebra.Smooth D (Localization.Away (p s₀)) := smooth_away_of_ker p hpsurj s₀ hkill
  have : Algebra.FinitePresentation D (MvPolynomial ι D ⧸ K) := by
    refine Algebra.FinitePresentation.quotient ?_
    rw [hK]
    exact (Submodule.fg_span (Set.finite_range _)).sup (Submodule.fg_span (Set.finite_range _))
  refine isSmoothAt_of_smooth_away hsm q ?_
  have hJ : p J ∉ q := hμ
  have hps' : p s ∉ q := by
    rw [hps]
    exact fun h ↦ hq (‹q.IsPrime›.mem_of_pow_mem _ h)
  have hpa : p (Ideal.Quotient.mk K₁ a) ∉ q := hq
  simp only [s₀, map_mul]
  exact ‹q.IsPrime›.mul_notMem hJ (‹q.IsPrime›.mul_notMem hps' hpa)

end StrictlyStandard

end Langlands.CommutativeAlgebra.Popescu.Desing
