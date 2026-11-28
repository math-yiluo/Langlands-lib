import Langlands.GroupScheme.Rational.NumberFieldQuaternionIntertwinerNorm
import Langlands.GroupScheme.Quaternionic.SkewHermitianQuadraticComponent
import Langlands.Global.RealCompletionWeakApproximation

/-! # Prescribed reduced norms and ellipticity at real places -/

noncomputable section

universe u

open scoped TensorProduct
open NumberField

namespace Langlands

section QuadraticFacts

/-- Over a field of characteristic different from two in which every element is a square,
a quadratic form on a finite-dimensional space of dimension at least two is isotropic. -/
theorem quadraticForm_not_anisotropic_of_forall_isSquare {K W : Type*} [Field K]
    [NeZero (2 : K)] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hsq : ∀ a : K, IsSquare a) (q : QuadraticForm K W) (hW : 2 ≤ Module.finrank K W) :
    ¬ q.Anisotropic := by
  intro han
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨e₁, he₁⟩ := exists_ne (0 : W)
  obtain ⟨e₂, hpair⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (by omega) he₁
  by_cases h₁ : q e₁ = 0
  · exact he₁ (han e₁ h₁)
  obtain ⟨s, hs⟩ := hsq (discrim (q e₁) (QuadraticMap.polar q e₁ e₂) (q e₂))
  set t := (-(QuadraticMap.polar q e₁ e₂) + s) / (2 * q e₁)
  have hroot : q e₁ * (t * t) + QuadraticMap.polar q e₁ e₂ * t + q e₂ = 0 :=
    (quadratic_eq_zero_iff h₁ hs t).mpr (Or.inl rfl)
  have hval : q (t • e₁ + e₂) = 0 := by
    rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_eq_mul,
      smul_eq_mul]
    linear_combination hroot
  have h := (LinearIndependent.pair_iff.mp hpair) t 1 (by rw [one_smul]; exact han _ hval)
  exact one_ne_zero h.2

/-- A quadratic form with an isotropic vector that is not orthogonal to everything represents
every scalar. -/
theorem quadraticForm_exists_eq_of_isotropic {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] (q : QuadraticForm K W) {y z : W} (hy : q y = 0)
    (hyz : QuadraticMap.polar q y z ≠ 0) (a : K) : ∃ x, q x = a := by
  refine ⟨((a - q z) / QuadraticMap.polar q y z) • y + z, ?_⟩
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.polar_smul_left, hy,
    smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hyz]
  ring

/-- The scalar extension of a nondegenerate bilinear form on a finite-dimensional space is
left-separating. -/
theorem bilinForm_baseChange_separatingLeft {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (K : Type*) [Field K] [Algebra F K]
    {B : LinearMap.BilinForm F V} (hB : B.Nondegenerate) :
    (B.baseChange K).SeparatingLeft := by
  intro x hx
  let b := Module.finBasis F V
  let f := B.dualBasis hB b
  let fK := Algebra.TensorProduct.basis K f
  apply fK.ext_elem
  intro i
  rw [map_zero, Finsupp.zero_apply]
  have h := hx ((1 : K) ⊗ₜ[F] b i)
  rw [← fK.sum_repr x, map_sum, LinearMap.sum_apply] at h
  simp only [map_smul, LinearMap.smul_apply, fK, Algebra.TensorProduct.basis_apply,
    LinearMap.BilinForm.baseChange_tmul, f, LinearMap.BilinForm.apply_dualBasis_left, mul_one,
    smul_eq_mul, ite_smul, one_smul, zero_smul, mul_ite, mul_zero] at h
  simpa using h

end QuadraticFacts

namespace Global

variable {F : Type u} [Field F]

/-- An element of a real completion with nonnegative real image is a square. -/
theorem realCompletion_isSquare_of_nonneg {v : InfinitePlace F} (hv : v.IsReal)
    {z : v.Completion} (hz : 0 ≤ InfinitePlace.Completion.extensionEmbeddingOfIsReal hv z) :
    IsSquare z := by
  set e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv
    (Real.sqrt (e z))
  refine ⟨y, e.injective ?_⟩
  rw [map_mul, hy, Real.mul_self_sqrt hz]

/-- An element of a real completion is a square or the negative of a square. -/
theorem realCompletion_isSquare_or_isSquare_neg {v : InfinitePlace F} (hv : v.IsReal)
    (z : v.Completion) : IsSquare z ∨ IsSquare (-z) := by
  rcases le_or_gt 0 (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv z) with h | h
  · exact Or.inl (realCompletion_isSquare_of_nonneg hv h)
  · exact Or.inr (realCompletion_isSquare_of_nonneg hv (by rw [map_neg]; linarith))

/-- In a real completion a sum of two squares vanishes only if both terms vanish. -/
theorem realCompletion_eq_zero_of_mul_self_add_mul_self {v : InfinitePlace F} (hv : v.IsReal)
    {a b : v.Completion} (h : a * a + b * b = 0) : a = 0 := by
  set e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  have h' : e a * e a + e b * e b = 0 := by rw [← map_mul, ← map_mul, ← map_add, h, map_zero]
  have ha : e a = 0 := by nlinarith [mul_self_nonneg (e a), mul_self_nonneg (e b)]
  exact e.injective (ha.trans (map_zero e).symm)

/-- Every element of a complex completion is a square. -/
theorem complexCompletion_isSquare {v : InfinitePlace F} (hv : v.IsComplex) (z : v.Completion) :
    IsSquare z := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  obtain ⟨y, hy⟩ := IsAlgClosed.isSquare (e z)
  exact ⟨e.symm y, e.injective (by rw [map_mul, RingEquiv.apply_symm_apply, hy])⟩

end Global

end Langlands

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

omit [NumberField F] [FiniteDimensional F D] [Algebra.IsCentral F D] in
/-- The scalar extension of the conjugate-product form on the whole algebra. -/
theorem conjugateProductQuadratic_baseChange [Invertible (2 : F)]
    (τ : FirstKindInvolution F D) (ℓ : D →ₗ[F] F) (R : Type u) [Field R] [Algebra F R] :
    QuadraticForm.baseChange R (conjugateProductQuadratic τ ℓ) =
      conjugateProductQuadratic (τ.baseChange R) (baseChangeScalarFunctional ℓ R) := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, conjugateProductQuadratic_apply,
    FirstKindInvolution.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    baseChangeScalarFunctional_tmul]

include hdim hsym in
/-- A scalar that is a square at every real place where the quaternion algebra stays a
division algebra is a reduced norm. -/
theorem exists_mul_conjugation_eq_of_real (a : F)
    (hsplit : ∀ v : InfinitePlace F, v.IsReal → ¬ IsSquare (algebraMap F v.Completion a) →
      ∃ y : v.Completion ⊗[F] D, y ≠ 0 ∧ ¬ IsUnit y) :
    ∃ d : D, d * σ.quaternionConjugation hdim hsym d = algebraMap F D a := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  set τ := σ.quaternionConjugation hdim hsym
  have hτ : ∀ x : D, x * τ x = algebraMap F D (reducedNorm F D F (1 ⊗ₜ[F] x)) :=
    σ.quaternionConjugation_norm hdim hsym
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap F D).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F D).injective)
  have hscalar (s : F) : ℓ (algebraMap F D s) = s := LinearMap.congr_fun hℓ s
  have h1 : ℓ (1 : D) = 1 := by simpa only [_root_.map_one] using hscalar 1
  let Q := conjugateProductQuadratic τ ℓ
  have hρ (x : D) : Q x = reducedNorm F D F (1 ⊗ₜ[F] x) := by
    change ℓ (x * τ x) = _
    rw [hτ, hscalar]
  have hzero (x : D) (hx : Q x = 0) : x = 0 := by
    have hp := hτ x
    rw [← hρ x, hx, _root_.map_zero] at hp
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact τ.injective (h.trans τ.map_zero.symm)
  have hnd : Q.polarBilin.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply hzero x
    have h := hx x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (two_ne_zero : (2 : F) ≠ 0)
  have hbase (R : Type u) [Field R] [Algebra F R] (y : R ⊗[F] D) :
      Q.baseChange R y = reducedNorm F D R y := by
    change QuadraticForm.baseChange R (conjugateProductQuadratic τ ℓ) y = _
    rw [conjugateProductQuadratic_baseChange, conjugateProductQuadratic_apply,
      σ.quaternionConjugation_norm_baseChange hdim hsym R y,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      baseChangeScalarFunctional_tmul, h1, one_smul]
  have hsq (R : Type u) [Field R] [Algebra F R] (h : IsSquare (algebraMap F R a)) :
      ∃ y, Q.baseChange R y = algebraMap F R a := by
    obtain ⟨s, hs⟩ := h
    refine ⟨s ⊗ₜ[F] (1 : D), ?_⟩
    rw [QuadraticForm.baseChange_tmul, hs]
    change ℓ (1 * τ 1) • (s * s) = s * s
    rw [τ.map_one, mul_one, h1, one_smul]
  have hloc (v : InfinitePlace F) : ∃ y, (Q.baseChange (Global.placeCompletion F (.inl v))) y =
      algebraMap F (Global.placeCompletion F (.inl v)) a := by
    change ∃ y, Q.baseChange v.Completion y = algebraMap F v.Completion a
    by_cases hv : v.IsReal
    · by_cases ha : IsSquare (algebraMap F v.Completion a)
      · exact hsq v.Completion ha
      · obtain ⟨y, hy0, hyu⟩ := hsplit v hv ha
        let K := v.Completion
        have h2K : (2 : K) ≠ 0 := by
          have h := (algebraMap F K).injective.ne (two_ne_zero : (2 : F) ≠ 0)
          rwa [map_ofNat, _root_.map_zero] at h
        let : Invertible (2 : K) := invertibleOfNonzero h2K
        have hN : reducedNorm F D K y = 0 := by
          by_contra hn
          apply hyu
          have : IsArtinianRing (K ⊗[F] D) := IsArtinianRing.of_finite K (K ⊗[F] D)
          set z := τ.baseChange K y * algebraMap K (K ⊗[F] D) (reducedNorm F D K y)⁻¹
          have hz : y * z = 1 := by
            rw [← mul_assoc, σ.quaternionConjugation_norm_baseChange hdim hsym K y,
              ← _root_.map_mul,
              mul_inv_cancel₀ hn, _root_.map_one]
          exact ⟨⟨y, z, hz, mul_eq_one_symm hz⟩, rfl⟩
        have hQy : Q.baseChange K y = 0 := by rw [hbase, hN]
        have hsep : (Q.baseChange K).polarBilin.SeparatingLeft := by
          rw [QuadraticForm.polarBilin_baseChange]
          exact Langlands.bilinForm_baseChange_separatingLeft K hnd
        obtain ⟨z, hz⟩ : ∃ z, QuadraticMap.polar (Q.baseChange K) y z ≠ 0 := by
          by_contra h
          push Not at h
          exact hy0 (hsep y fun z => by rw [QuadraticMap.polarBilin_apply_apply]; exact h z)
        exact Langlands.quadraticForm_exists_eq_of_isotropic _ hQy hz _
    · exact hsq v.Completion (Langlands.Global.complexCompletion_isSquare
        (InfinitePlace.not_isReal_iff_isComplex.mp hv) _)
  have hrank : 4 ≤ Module.finrank F D := hdim.ge
  obtain ⟨d, hd⟩ := Langlands.numberFieldQuadraticRepresentation_of_archimedean Q hnd hrank a hloc
  refine ⟨d, ?_⟩
  rw [hτ, ← hρ, hd]

omit [NumberField F] [FiniteDimensional F D] [Algebra.IsCentral F D] in
/-- Expansion of a bilinear map in the coordinates of a basis. -/
theorem bilin_eq_sum_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι F D)
    (β : D →ₗ[F] D →ₗ[F] F) (x y : D) :
    β x y = ∑ i, ∑ j, b.repr x i * b.repr y j * β (b i) (b j) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [_root_.map_sum, _root_.map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [NumberField F] [FiniteDimensional F D] [Algebra.IsCentral F D] in
/-- If `d + τ(d)` and `d τ(d)` are scalars `t` and `n`, then `(d - τ(d))² = t² - 4n`. -/
theorem sub_conjugation_mul_self (τ : FirstKindInvolution F D) (ℓ : D →ₗ[F] F)
    (d : D) (ht : d + τ d = algebraMap F D (ℓ (d + τ d)))
    (hn : d * τ d = algebraMap F D (ℓ (d * τ d))) :
    (d - τ d) * (d - τ d) = algebraMap F D (ℓ (d + τ d) ^ 2 - 4 * ℓ (d * τ d)) := by
  set N := ℓ (d * τ d)
  set T := algebraMap F D (ℓ (d + τ d))
  have hτd : τ d = T - d := by rw [← ht]; abel
  have hTd : T * d = d * T := Algebra.commutes _ _
  calc (d - τ d) * (d - τ d) = (d - (T - d)) * (d - (T - d)) := by rw [hτd]
    _ = 4 * (d * d) - 2 * (d * T) - 2 * (T * d) + T * T := by noncomm_ring
    _ = T * T - 4 * (d * (T - d)) := by rw [hTd]; noncomm_ring
    _ = T * T - 4 * algebraMap F D N := by rw [← hτd, hn]
    _ = _ := by
      rw [_root_.map_sub, _root_.map_mul, _root_.map_pow, map_ofNat (algebraMap F D) 4, sq]

include hdim hsym in
/-- At every real place some quaternion of the conjugation's alternating subspace has positive
reduced norm. -/
theorem exists_alternating_pos_norm_of_isReal {v : InfinitePlace F} (hv : v.IsReal) :
    ∃ u : D, σ.quaternionConjugation hdim hsym u = -u ∧ ∃ n : F,
      u * σ.quaternionConjugation hdim hsym u = algebraMap F D n ∧
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (algebraMap F v.Completion n) := by
  set τ := σ.quaternionConjugation hdim hsym
  set l : D := (KneserThree.Quaternion.ell σ hdim hsym : D)
  obtain ⟨Q, hQx, hbar⟩ := KneserThree.Quaternion.exists_quatData_of_pure σ hdim hsym
    two_ne_zero (KneserThree.Quaternion.ell σ hdim hsym).ne_zero
    (KneserThree.Quaternion.conj_ell σ hdim hsym)
  set φ : F →+* ℝ := (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (algebraMap F v.Completion)
  have hx : τ Q.x = -Q.x := by rw [hQx]; exact KneserThree.Quaternion.conj_ell σ hdim hsym
  have hj : τ Q.j = -Q.j := by
    have hfj : Q.fst Q.j = 0 := by simpa using Q.fst_j_mul 1
    have hsj : Q.snd Q.j = 1 := by simpa using Q.snd_j_mul 1
    rw [hbar, ← Q.decompose (Q.bar Q.j), KneserThree.QuatData.fst_bar,
      KneserThree.QuatData.snd_bar, hfj, hsj, _root_.map_zero, _root_.map_zero, zero_add,
      _root_.map_neg, _root_.map_one, mul_neg, mul_one]
  have hxne : Q.x ≠ 0 := by
    have hb := Q.basis.ne_zero 1
    rwa [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hb
  have hjne : Q.j ≠ 0 := by
    have hb := Q.basis.ne_zero 2
    rwa [show Q.basis 2 = Q.j from congrFun Q.basis_eq 2] at hb
  have hc : Q.c ≠ 0 := by
    intro h
    have := Q.x_mul_x
    rw [h, _root_.map_zero] at this
    exact hxne (mul_self_eq_zero.mp this)
  have hδ : Q.δ ≠ 0 := by
    intro h
    have := Q.j_mul_j
    rw [h, _root_.map_zero] at this
    exact hjne (mul_self_eq_zero.mp this)
  have hφc : φ Q.c ≠ 0 := (map_ne_zero φ).mpr hc
  have hφδ : φ Q.δ ≠ 0 := (map_ne_zero φ).mpr hδ
  rcases lt_or_gt_of_ne hφc with hc0 | hc0
  · refine ⟨Q.x, hx, -Q.c, ?_, ?_⟩
    · rw [hx, mul_neg, Q.x_mul_x, _root_.map_neg]
    · change 0 < φ (-Q.c)
      rw [_root_.map_neg]
      linarith
  rcases lt_or_gt_of_ne hφδ with hδ0 | hδ0
  · refine ⟨Q.j, hj, -Q.δ, ?_, ?_⟩
    · rw [hj, mul_neg, Q.j_mul_j, _root_.map_neg]
    · change 0 < φ (-Q.δ)
      rw [_root_.map_neg]
      linarith
  · refine ⟨Q.j * Q.x, ?_, Q.c * Q.δ, ?_, ?_⟩
    · rw [τ.map_mul, hx, hj, neg_mul_neg, Q.j_mul_x, neg_neg]
    · rw [τ.map_mul, hx, hj, neg_mul_neg, ← mul_assoc, mul_assoc Q.j, Q.x_mul_x,
        ← Algebra.commutes, mul_assoc, Q.j_mul_j, ← _root_.map_mul]
    · change 0 < φ (Q.c * Q.δ)
      rw [_root_.map_mul]
      exact mul_pos hc0 hδ0


include hdim hsym in
/-- A nonzero scalar that is a square at every real place where the quaternion algebra stays a
division algebra is, up to a nonzero square factor, the reduced norm of a quaternion `d` whose
defect `d - τ d` squares to a scalar that is negative at every real place where the given
scalar is a square. -/
theorem exists_elliptic_mul_conjugation (a : F) (ha : a ≠ 0)
    (hsplit : ∀ v : InfinitePlace F, v.IsReal → ¬ IsSquare (algebraMap F v.Completion a) →
      ∃ y : v.Completion ⊗[F] D, y ≠ 0 ∧ ¬ IsUnit y) :
    ∃ (d : D) (s c : F), s ≠ 0 ∧
      d * σ.quaternionConjugation hdim hsym d = algebraMap F D (a * s ^ 2) ∧
      (d - σ.quaternionConjugation hdim hsym d) * (d - σ.quaternionConjugation hdim hsym d) =
        algebraMap F D c ∧
      ∀ (v : InfinitePlace F) (hv : v.IsReal), IsSquare (algebraMap F v.Completion a) →
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (algebraMap F v.Completion c) < 0 := by
  classical
  set τ := σ.quaternionConjugation hdim hsym
  obtain ⟨d₀, hd₀⟩ := σ.exists_mul_conjugation_eq_of_real hdim hsym a hsplit
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap F D).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F D).injective)
  have hscalar (s : F) : ℓ (algebraMap F D s) = s := LinearMap.congr_fun hℓ s
  have h1 : ℓ (1 : D) = 1 := by simpa only [_root_.map_one] using hscalar 1
  have hnorm (x : D) : x * τ x = algebraMap F D (ℓ (x * τ x)) := by
    rw [σ.quaternionConjugation_norm hdim hsym, hscalar]
  have htrace (x : D) : x + τ x = algebraMap F D (ℓ (x + τ x)) := by
    obtain ⟨t, ht⟩ := KneserThree.Quaternion.add_conj_mem σ hdim hsym x
    rw [ht, hscalar]
  have hdefect (d : D) (s : F) (hd : d * τ d = algebraMap F D (a * s ^ 2)) :
      (d - τ d) * (d - τ d) = algebraMap F D (ℓ (d + τ d) ^ 2 - 4 * (a * s ^ 2)) := by
    have h := sub_conjugation_mul_self τ ℓ d (htrace d) (hnorm d)
    rwa [hd, hscalar] at h
  by_cases hT : ∃ v : InfinitePlace F, v.IsReal ∧ IsSquare (algebraMap F v.Completion a)
  swap
  · push Not at hT
    have hd₁ : d₀ * τ d₀ = algebraMap F D (a * 1 ^ 2) := by rw [hd₀, one_pow, mul_one]
    exact ⟨d₀, 1, _, one_ne_zero, hd₁, hdefect d₀ 1 hd₁, fun v hv hsq => absurd hsq (hT v hv)⟩
  let n := Module.finrank F D
  let b := Module.finBasis F D
  let βN : D →ₗ[F] D →ₗ[F] F :=
    ((LinearMap.mul F D).compl₁₂ LinearMap.id τ.toLinearMap).compr₂ ℓ
  let βT : D →ₗ[F] D →ₗ[F] F :=
    (((LinearMap.mul F D).compl₁₂ (LinearMap.mulLeft F d₀) LinearMap.id).compr₂
      (LinearMap.id + τ.toLinearMap)).compr₂ ℓ
  have hβN (x y : D) : βN x y = ℓ (x * τ y) := rfl
  have hβT (x y : D) : βT x y = ℓ (d₀ * x * y + τ (d₀ * x * y)) := rfl
  let e (w : {w : InfinitePlace F // w.IsReal}) :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
  let φ (w : {w : InfinitePlace F // w.IsReal}) : F →+* ℝ :=
    (e w).comp (algebraMap F w.1.Completion)
  let quad (w : {w : InfinitePlace F // w.IsReal}) (β : D →ₗ[F] D →ₗ[F] F) (r : Fin n → ℝ) : ℝ :=
    ∑ i, ∑ j, r i * r j * φ w (β (b i) (b j))
  let P (w : {w : InfinitePlace F // w.IsReal}) (r : Fin n → ℝ) : ℝ :=
    quad w βT r ^ 2 - 4 * φ w a * quad w βN r ^ 2
  have hquad (w : {w : InfinitePlace F // w.IsReal}) (β : D →ₗ[F] D →ₗ[F] F) (x : D) :
      quad w β (fun i => φ w (b.repr x i)) = φ w (β x x) := by
    rw [bilin_eq_sum_repr b β x x]
    simp only [quad, _root_.map_sum, _root_.map_mul]
    rfl
  have hline (w : {w : InfinitePlace F // w.IsReal}) (β : D →ₗ[F] D →ₗ[F] F) (x u : D) (s : ℝ) :
      quad w β (fun i => φ w (b.repr x i) + s * φ w (b.repr u i)) =
        φ w (β x x) + s * (φ w (β x u) + φ w (β u x)) + s ^ 2 * φ w (β u u) := by
    rw [bilin_eq_sum_repr b β x x, bilin_eq_sum_repr b β x u, bilin_eq_sum_repr b β u x,
      bilin_eq_sum_repr b β u u]
    simp only [quad, _root_.map_sum, _root_.map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlocal (w : {w : InfinitePlace F // w.IsReal})
      (hw : IsSquare (algebraMap F w.1.Completion a)) : ∃ r : Fin n → ℝ, P w r < 0 := by
    have hφa : 0 < φ w a := by
      obtain ⟨t, ht⟩ := hw
      have h0 : φ w a = e w t * e w t := by
        simp only [φ, RingHom.comp_apply, ht, _root_.map_mul]
      have hne : φ w a ≠ 0 := (map_ne_zero (φ w)).mpr ha
      rw [h0] at hne ⊢
      exact lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm hne)
    obtain ⟨u, hu, m, hm, hmpos⟩ := σ.exists_alternating_pos_norm_of_isReal hdim hsym w.2
    have hk : 0 < φ w m := hmpos
    have hN11 : βN 1 1 = 1 := by rw [hβN, τ.map_one, mul_one, h1]
    have hN1u : βN 1 u + βN u 1 = 0 := by
      rw [hβN, hβN, one_mul, τ.map_one, mul_one, hu, _root_.map_neg, neg_add_cancel]
    have hNuu : βN u u = m := by rw [hβN, hm, hscalar]
    have huu : u * u = -algebraMap F D m := by rw [← hm, hu, mul_neg, neg_neg]
    have hduu : d₀ * u * u = -(m • d₀) := by
      rw [mul_assoc, huu, mul_neg, ← Algebra.commutes, ← Algebra.smul_def]
    have hTuu : βT u u = -(m * βT 1 1) := by
      rw [hβT, hβT, hduu, τ.map_neg, τ.map_smul, mul_one, mul_one, ← neg_add, ← smul_add,
        _root_.map_neg, _root_.map_smul, smul_eq_mul]
    set A := φ w (βT 1 1)
    set B' := φ w (βT 1 u) + φ w (βT u 1)
    set k := φ w m
    obtain ⟨s, hs⟩ : ∃ s : ℝ, A + s * B' + s ^ 2 * (-(k * A)) = 0 := by
      by_cases hA : A = 0
      · exact ⟨0, by rw [hA]; ring⟩
      · have hlead : -(k * A) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hk.ne' hA)
        have hdisc : discrim (-(k * A)) B' A =
            Real.sqrt (B' ^ 2 + 4 * k * A ^ 2) * Real.sqrt (B' ^ 2 + 4 * k * A ^ 2) := by
          rw [Real.mul_self_sqrt (by positivity), discrim]
          ring
        refine ⟨(-B' + Real.sqrt (B' ^ 2 + 4 * k * A ^ 2)) / (2 * -(k * A)), ?_⟩
        have h := (quadratic_eq_zero_iff hlead hdisc _).mpr (Or.inl rfl)
        linear_combination h
    refine ⟨fun i => φ w (b.repr 1 i) + s * φ w (b.repr u i), ?_⟩
    have hT' : quad w βT (fun i => φ w (b.repr 1 i) + s * φ w (b.repr u i)) = 0 := by
      rw [hline, hTuu, _root_.map_neg, _root_.map_mul]
      linear_combination hs
    have hN' : quad w βN (fun i => φ w (b.repr 1 i) + s * φ w (b.repr u i)) = 1 + s ^ 2 * k := by
      rw [hline, ← _root_.map_add, hN1u, hN11, hNuu, _root_.map_one, _root_.map_zero]
      ring
    simp only [P]
    rw [hT', hN']
    have hpos : 0 < 1 + s ^ 2 * k := by positivity
    nlinarith [mul_pos hφa (pow_pos hpos 2)]
  let U (w : {w : InfinitePlace F // w.IsReal}) : Set (Fin n → w.1.Completion) :=
    if IsSquare (algebraMap F w.1.Completion a) then {z | P w (fun i => e w (z i)) < 0}
    else Set.univ
  have hcont (w : {w : InfinitePlace F // w.IsReal}) :
      Continuous (fun z : Fin n → w.1.Completion => P w (fun i => e w (z i))) := by
    have he : Continuous (e w) :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous
    simp only [P, quad]
    fun_prop
  have hU (w : {w : InfinitePlace F // w.IsReal}) : IsOpen (U w) := by
    simp only [U]
    split_ifs
    · exact isOpen_lt (hcont w) continuous_const
    · exact isOpen_univ
  have hUn (w : {w : InfinitePlace F // w.IsReal}) : (U w).Nonempty := by
    simp only [U]
    split_ifs with hw
    · obtain ⟨r, hr⟩ := hlocal w hw
      choose z hz using fun i =>
        InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal w.2 (r i)
      refine ⟨z, ?_⟩
      change P w (fun i => e w (z i)) < 0
      have : (fun i => e w (z i)) = r := funext hz
      rw [this]
      exact hr
    · exact Set.univ_nonempty
  obtain ⟨γ, hγ⟩ := (Global.realCompletionVectorWeakApproximation F n).exists_mem_open
    (isOpen_set_pi Set.finite_univ fun w _ => hU w) (Set.univ_pi_nonempty_iff.mpr hUn)
  set y := ∑ i, γ i • b i
  have hyrepr : ⇑(b.repr y) = γ := b.repr_sum_self γ
  set d := d₀ * y * y with hd_def
  set s := βN y y with hs_def
  set t := βT y y with ht_def
  have hys : y * τ y = algebraMap F D s := hnorm y
  have hd : d * τ d = algebraMap F D (a * s ^ 2) := by
    have hc (z : D) : z * algebraMap F D s = algebraMap F D s * z := (Algebra.commutes _ _).symm
    have hτd : τ d = τ y * (τ y * τ d₀) := by rw [hd_def, τ.map_mul, τ.map_mul]
    calc d * τ d = d₀ * y * (y * τ y) * τ y * τ d₀ := by
          rw [hτd, hd_def]
          noncomm_ring
      _ = algebraMap F D s * (d₀ * (y * τ y) * τ d₀) := by
          conv_lhs => rw [hys]
          rw [hc (d₀ * y)]
          noncomm_ring
      _ = algebraMap F D s * (algebraMap F D s * (d₀ * τ d₀)) := by
          rw [hys, hc d₀, mul_assoc]
      _ = algebraMap F D (a * s ^ 2) := by
          rw [hd₀, ← _root_.map_mul, ← _root_.map_mul]
          congr 1
          ring
  have hval (w : {w : InfinitePlace F // w.IsReal})
      (hw : IsSquare (algebraMap F w.1.Completion a)) :
      P w (fun i => φ w (γ i)) < 0 := by
    have h := hγ w (Set.mem_univ _)
    simp only [U, hw, ↓reduceIte] at h
    exact h
  have hPval (w : {w : InfinitePlace F // w.IsReal}) :
      P w (fun i => φ w (γ i)) = φ w (t ^ 2 - 4 * (a * s ^ 2)) := by
    have hT1 := hquad w βT y
    have hN1 := hquad w βN y
    rw [hyrepr] at hT1 hN1
    simp only [P]
    rw [hT1, hN1, ← ht_def, ← hs_def, _root_.map_sub, _root_.map_mul, _root_.map_mul,
      _root_.map_pow, _root_.map_pow, map_ofNat]
    ring
  obtain ⟨v₀, hv₀, hsq₀⟩ := hT
  have hs0 : s ≠ 0 := by
    intro h0
    have h := hval ⟨v₀, hv₀⟩ hsq₀
    rw [hPval, h0] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      _root_.map_pow] at h
    exact absurd h (not_lt.mpr (sq_nonneg _))
  refine ⟨d, s, t ^ 2 - 4 * (a * s ^ 2), hs0, hd, hdefect d s hd, fun v hv hsq => ?_⟩
  have h := hval ⟨v, hv⟩ hsq
  rw [hPval] at h
  exact h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
