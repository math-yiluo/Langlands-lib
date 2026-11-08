import Langlands.AlgebraicGeometry.PointTopology.HenselianIffSeparablyClosedProof
import Langlands.FieldTheory.RealClosedIrreducibleDegree
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Archimedean henselian fields

An archimedean nontrivially normed field `K` is henselian exactly when it has a ring map
`σ : K → ℂ` with `‖x‖ = ‖σ x‖ ^ s` for some `0 < s ≤ 1`, and either `K` is algebraically closed,
or `σ` is real and `K` is real closed.

* Forward direction. The completion `K̂` is complete and archimedean. So it has such a map
  `φ : K̂ → ℂ`, and the extension `ψ : ℝ → K̂` of `ℚ → K̂` satisfies `φ ∘ ψ = id`. The field `K`
  is separably closed in `K̂` and has characteristic `0`, so every element of `K̂` algebraic over
  `K` lies in `K`. If `σ = φ|_K` is real, square roots and roots of odd-degree polynomials are
  found in `ℝ`, carried to `K̂` by `ψ`, and lie in `K`, so `K` is real closed. Otherwise `φ` is
  onto `ℂ`, and roots in `ℂ` give roots in `K`, so `K` is algebraically closed.
* Backward direction. If `K` is algebraically closed, it is separably closed in `K̂`. If `K` is
  real closed with real `σ`, irreducible polynomials over `K` have degree at most `2`. The
  extension of `σ` to `K̂` is real, and an irreducible quadratic has negative discriminant, so it
  has no root in `K̂`. Either way the separable-closedness criterion applies.
-/

noncomputable section

universe u

open Polynomial Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianArchimedean

/-- A real polynomial of odd degree has a real root. -/
theorem real_exists_isRoot_of_odd {f : ℝ[X]} (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  wlog hlc : 0 ≤ f.leadingCoeff generalizing f
  · obtain ⟨x, hx⟩ := this (f := -f) (by rwa [natDegree_neg])
      (by rw [leadingCoeff_neg]; linarith)
    exact ⟨x, by simpa using hx⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hf
    exact Nat.not_odd_zero hf
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hf.pos
  have h1 := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg f hdeg hlc
  have hX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  let g := f.comp (-X)
  have hgdeg : g.natDegree = f.natDegree := by
    simp only [g, natDegree_comp, hX, mul_one]
  have hglc : g.leadingCoeff = -f.leadingCoeff := by
    simp only [g]
    rw [leadingCoeff_comp (by rw [hX]; exact one_ne_zero), leadingCoeff_neg, leadingCoeff_X,
      hf.neg_one_pow, mul_neg_one]
  have h2 := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos g
    (natDegree_pos_iff_degree_pos.mp (hgdeg ▸ hf.pos)) (by rw [hglc]; linarith)
  obtain ⟨b, hb⟩ := (h1.eventually (eventually_ge_atTop 0)).exists
  obtain ⟨a, ha⟩ := (h2.eventually (eventually_le_atBot 0)).exists
  have ha' : f.eval (-a) ≤ 0 := by simpa [g, eval_comp] using ha
  obtain ⟨c, hc⟩ := intermediate_value_univ (-a) b f.continuous ⟨ha', hb⟩
  exact ⟨c, hc⟩

variable {K : Type u} [NontriviallyNormedField K]

/-- A map with `‖x‖ = ‖σ x‖ ^ s` is uniformly continuous. -/
theorem uniformContinuous_of_rpow (σ : K →+* ℂ) {s : ℝ} (hs0 : 0 < s)
    (hσ : ∀ x, ‖x‖ = ‖σ x‖ ^ s) : UniformContinuous σ := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε ^ s, Real.rpow_pos_of_pos hε s, fun {a b} h => ?_⟩
  rw [dist_eq_norm, hσ, map_sub] at h
  rw [dist_eq_norm]
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hs0).mp h

/-- The real part of a real-valued map to `ℂ`, as a ring map to `ℝ`. -/
def realPart (σ : K →+* ℂ) (hreal : ∀ x, (σ x).im = 0) : K →+* ℝ where
  toFun x := (σ x).re
  map_one' := by rw [map_one, Complex.one_re]
  map_mul' x y := by rw [map_mul, Complex.mul_re, hreal x, hreal y, mul_zero, sub_zero]
  map_zero' := by rw [map_zero, Complex.zero_re]
  map_add' x y := by rw [map_add, Complex.add_re]

theorem ofReal_realPart (σ : K →+* ℂ) (hreal : ∀ x, (σ x).im = 0) (x : K) :
    ((realPart σ hreal x : ℝ) : ℂ) = σ x :=
  Complex.ext (by simp [realPart]) (by simp [realPart, hreal x])

local notation "K̂" => UniformSpace.Completion K

/-- With `K` separably closed in `K̂` and of characteristic `0`, an element of `K̂` that is a root
of a nonzero polynomial over `K` lies in `K`. -/
theorem mem_range_of_aeval_eq_zero [CharZero K] (hsep : separableClosure K K̂ = ⊥) {p : K[X]}
    (hp : p ≠ 0) {y : K̂} (hy : aeval y p = 0) : y ∈ Set.range (algebraMap K K̂) := by
  have hint : IsIntegral K y := (show IsAlgebraic K y from ⟨p, hp, hy⟩).isIntegral
  have hys : IsSeparable K y := (minpoly.irreducible hint).separable
  have : y ∈ separableClosure K K̂ := mem_separableClosure_iff.mpr hys
  rw [hsep] at this
  exact IntermediateField.mem_bot.mp this

/-- A polynomial over `K` with a root in `K̂` has a root in `K`. -/
theorem exists_root_of_aeval_eq_zero [CharZero K] (hsep : separableClosure K K̂ = ⊥) {p : K[X]}
    (hp : p ≠ 0) {y : K̂} (hy : aeval y p = 0) : ∃ z : K, p.eval z = 0 := by
  obtain ⟨z, rfl⟩ := mem_range_of_aeval_eq_zero hsep hp hy
  refine ⟨z, (algebraMap K K̂).injective ?_⟩
  rw [map_zero, ← hy, aeval_algebraMap_apply, coe_aeval_eq_eval]

/-! ### The backward direction -/

/-- An algebraically closed field is separably closed in its completion. -/
theorem separableClosure_eq_bot_of_isAlgClosed [IsAlgClosed K] :
    separableClosure K K̂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hint : IsIntegral K x := (mem_separableClosure_iff.mp hx).isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  rw [IntermediateField.mem_bot]
  exact minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)

/-- A real closed field with a real power-isometric map to `ℂ` is separably closed in its
completion. -/
theorem separableClosure_eq_bot_of_isRealClosed [IsRealClosed K] (σ : K →+* ℂ) {s : ℝ}
    (hs0 : 0 < s) (hσ : ∀ x, ‖x‖ = ‖σ x‖ ^ s) (hreal : ∀ x, (σ x).im = 0) :
    separableClosure K K̂ = ⊥ := by
  have hσc : Continuous σ := (uniformContinuous_of_rpow σ hs0 hσ).continuous
  let σ' := UniformSpace.Completion.extensionHom σ hσc
  have hσ'c : Continuous σ' := UniformSpace.Completion.continuous_extension
  have hσ'coe : ∀ x : K, σ' (x : K̂) = σ x := UniformSpace.Completion.extensionHom_coe σ hσc
  have hσ'real : ∀ y : K̂, (σ' y).im = 0 := fun y =>
    UniformSpace.Completion.induction_on y
      (isClosed_eq (Complex.continuous_im.comp hσ'c) continuous_const)
      (fun x => by rw [hσ'coe]; exact hreal x)
  rw [eq_bot_iff]
  intro x hx
  have hint : IsIntegral K x := (mem_separableClosure_iff.mp hx).isIntegral
  set m := minpoly K x with hm
  have hle : m.natDegree ≤ 2 :=
    Langlands.FieldTheory.RealClosedDegree.natDegree_le_two_of_irreducible (realPart σ hreal)
      (minpoly.irreducible hint)
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  rw [IntermediateField.mem_bot]
  by_contra hxK
  have hne1 : m.natDegree ≠ 1 := fun h1 => hxK (minpoly.natDegree_eq_one_iff.mp h1)
  have h2 : m.natDegree = 2 := by omega
  -- `x ^ 2 + b x + c = 0`
  set b := m.coeff 1
  set c := m.coeff 0
  have hbc : x * x + algebraMap K K̂ b * x + algebraMap K K̂ c = 0 := by
    have hev : aeval x m = 0 := minpoly.aeval K x
    rw [aeval_eq_sum_range, h2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at hev
    have hc2 : m.coeff 2 = 1 := by
      rw [← h2]
      exact (minpoly.monic hint).coeff_natDegree
    rw [hc2, one_smul, pow_zero, pow_one, Algebra.smul_def, Algebra.smul_def, mul_one] at hev
    linear_combination hev
  set δ := b * b - 4 * c with hδ
  have hγδ : (2 * x + algebraMap K K̂ b) * (2 * x + algebraMap K K̂ b) = algebraMap K K̂ δ := by
    rw [hδ]
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination 4 * hbc
  have h2K : (2 : K̂) ≠ 0 := by
    rw [← map_ofNat (algebraMap K K̂) 2]
    exact (_root_.map_ne_zero _).mpr two_ne_zero
  -- `δ` is not a square, so `-δ` is
  have hnsq : ¬ IsSquare δ := by
    rintro ⟨t, ht⟩
    have : (2 * x + algebraMap K K̂ b - algebraMap K K̂ t) *
        (2 * x + algebraMap K K̂ b + algebraMap K K̂ t) = 0 := by
      have : algebraMap K K̂ t * algebraMap K K̂ t = algebraMap K K̂ δ := by rw [← map_mul, ← ht]
      linear_combination hγδ - this
    apply hxK
    rcases mul_eq_zero.mp this with h | h
    · refine ⟨(t - b) / 2, ?_⟩
      rw [map_div₀, map_sub, map_ofNat, div_eq_iff h2K]
      linear_combination -h
    · refine ⟨(-t - b) / 2, ?_⟩
      rw [map_div₀, map_sub, map_neg, map_ofNat, div_eq_iff h2K]
      linear_combination -h
  obtain ⟨e, he⟩ := (IsRealClosed.isSquare_or_isSquare_neg δ).resolve_left hnsq
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hnsq
    rw [mul_zero, neg_eq_zero] at he
    exact ⟨0, by rw [he, mul_zero]⟩
  -- apply the real map `σ'`
  have hδe : algebraMap K K̂ δ = -(algebraMap K K̂ e * algebraMap K K̂ e) := by
    rw [← map_mul, ← he, map_neg, neg_neg]
  rw [hδe] at hγδ
  have hC := congrArg σ' hγδ
  rw [map_mul, map_neg, map_mul, show σ' (algebraMap K K̂ e) = σ e from hσ'coe e] at hC
  set u := σ' (2 * x + algebraMap K K̂ b)
  have hre := congrArg Complex.re hC
  simp only [Complex.mul_re, Complex.neg_re, hreal e, mul_zero, sub_zero] at hre
  rw [show u.im = 0 from hσ'real _, mul_zero, sub_zero] at hre
  have hσe : (σ e).re = 0 := by nlinarith [mul_self_nonneg u.re, mul_self_nonneg (σ e).re]
  have : σ e = 0 := Complex.ext hσe (hreal e)
  exact he0 ((map_eq_zero σ).mp this)

/-! ### The forward direction -/

theorem map_aeval {L : Type*} [Field L] (φ : K̂ →+* L) (f : K[X]) (y : K̂) :
    φ (aeval y f) = f.eval₂ (φ.comp (algebraMap K K̂)) (φ y) := by
  rw [aeval_def, hom_eval₂]

/-- **An archimedean henselian field** has a power-isometric map to `ℂ`, and is algebraically
closed, or real closed with a real map. -/
theorem exists_of_isHenselianValuedField (h : ¬ IsUltrametricDist K)
    (hK : IsHenselianValuedField K) :
    ∃ (σ : K →+* ℂ) (s : ℝ), 0 < s ∧ s ≤ 1 ∧ (∀ x, ‖x‖ = ‖σ x‖ ^ s) ∧
      (IsAlgClosed K ∨ ((∀ x, (σ x).im = 0) ∧ IsRealClosed K)) := by
  obtain ⟨hcK, -⟩ := CompleteHenselian.exists_rpow_of_not_ultrametric h
  let _ := HenselianIffSeparablyClosed.completionNormedField K
  have hc : ¬ IsUltrametricDist K̂ := by
    intro hc
    apply h
    refine IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n => ?_
    have h1 := IsUltrametricDist.norm_natCast_le_one K̂ n
    rwa [show ((n : K̂)) = ((n : K) : K̂) from
      (map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n).symm,
      UniformSpace.Completion.norm_coe] at h1
  obtain ⟨hchar, s, hs0, hs1, hrat⟩ := CompleteHenselian.exists_rpow_of_not_ultrametric hc
  obtain ⟨φ, hφ⟩ := CompleteHenselian.exists_complex_rpow hs0 hs1 hrat
  let σ : K →+* ℂ := φ.comp (algebraMap K K̂)
  have hσ : ∀ x, ‖x‖ = ‖σ x‖ ^ s := fun x => by
    rw [← UniformSpace.Completion.norm_coe]
    exact hφ _
  have hφc : Continuous φ := (uniformContinuous_of_rpow φ hs0 hφ).continuous
  let ψ := CompleteHenselian.realHom hs0 hrat
  have hψc : Continuous ψ := CompleteHenselian.continuous_realHom hs0 hrat
  have hφψ : ∀ r : ℝ, φ (ψ r) = (r : ℂ) := by
    have heq := Rat.denseRange_cast.equalizer (hφc.comp hψc) Complex.continuous_ofReal
      (funext fun q => by simp [map_ratCast])
    exact fun r => congrFun heq r
  have hsep : separableClosure K K̂ = ⊥ := separableClosure_completion_eq_bot K hK
  refine ⟨σ, s, hs0, hs1, hσ, ?_⟩
  by_cases hreal : ∀ x, (σ x).im = 0
  · -- the real case: `K` is real closed
    refine Or.inr ⟨hreal, ?_⟩
    let τ := realPart σ hreal
    have hτσ : ∀ x, ((τ x : ℝ) : ℂ) = σ x := ofReal_realPart σ hreal
    have hστ : σ = Complex.ofRealHom.comp τ := by
      ext x
      exact (hτσ x).symm
    have hψ : ∀ x : K, ψ (τ x) = algebraMap K K̂ x := by
      intro x
      apply φ.injective
      rw [hφψ, hτσ]
      rfl
    have hsq : ∀ x : K, 0 ≤ τ x → IsSquare x := by
      intro x hx
      set y := ψ (Real.sqrt (τ x))
      have hy : y * y = algebraMap K K̂ x := by
        rw [← map_mul, Real.mul_self_sqrt hx, hψ]
      obtain ⟨z, hz⟩ := mem_range_of_aeval_eq_zero hsep (X_pow_sub_C_ne_zero two_pos x)
        (y := y) (by rw [map_sub, aeval_X_pow, aeval_C, sq, hy, sub_self])
      refine ⟨z, (algebraMap K K̂).injective ?_⟩
      rw [map_mul, hz, hy]
    exact
      { toIsSemireal := IsSemireal.of_not_isSumSq_neg_one (by
          intro hsum
          have hnn : ∀ t : K, IsSumSq t → 0 ≤ τ t := by
            intro t ht
            induction ht with
            | zero => rw [map_zero]
            | sq_add a _ ih =>
              rw [map_add, map_mul]
              nlinarith [mul_self_nonneg (τ a)]
          have := hnn _ hsum
          rw [map_neg, map_one] at this
          linarith)
        isSquare_or_isSquare_neg := fun x => by
          rcases le_total 0 (τ x) with hx | hx
          · exact Or.inl (hsq x hx)
          · exact Or.inr (hsq (-x) (by rw [map_neg]; linarith))
        exists_isRoot_of_odd_natDegree := fun {f} hf => by
          have hf0 : f ≠ 0 := by
            rintro rfl
            rw [natDegree_zero] at hf
            exact Nat.not_odd_zero hf
          obtain ⟨t, ht⟩ := real_exists_isRoot_of_odd (f := f.map τ)
            (by rwa [natDegree_map_eq_of_injective τ.injective])
          obtain ⟨z, hz⟩ := exists_root_of_aeval_eq_zero hsep hf0 (y := ψ t) (by
            apply φ.injective
            rw [map_aeval, map_zero, hφψ]
            change f.eval₂ σ (t : ℂ) = 0
            rw [hστ, ← Complex.ofRealHom_eq_coe, ← hom_eval₂, ← eval_map, ht.eq_zero, map_zero])
          exact ⟨z, hz⟩ }
  · -- the non-real case: `K` is algebraically closed
    left
    push Not at hreal
    obtain ⟨x₀, hx₀⟩ := hreal
    refine IsAlgClosed.of_exists_root K fun p hp hirr => ?_
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (p.map σ)
      (by rw [degree_map]; exact (degree_pos_of_irreducible hirr).ne')
    set w₀ := σ x₀
    set b := w.im / w₀.im
    set a := w.re - b * w₀.re
    set y : K̂ := ψ a + ψ b * algebraMap K K̂ x₀
    have hφy : φ y = w := by
      have : φ (algebraMap K K̂ x₀) = w₀ := rfl
      rw [map_add, map_mul, hφψ, hφψ, this]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
          sub_zero, a]
        ring
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
          zero_mul, add_zero, b]
        field_simp
    exact exists_root_of_aeval_eq_zero hsep hp.ne_zero (y := y) (by
      apply φ.injective
      rw [map_aeval, map_zero, hφy]
      change p.eval₂ σ w = 0
      rw [← eval_map]
      exact hw)

end HenselianArchimedean

/-- **The archimedean henselian fields** (Conrad, printed p.14): an archimedean `K` is henselian
exactly when it has a map `σ` to `ℂ` with `‖x‖ = ‖σ x‖ ^ s`, `0 < s ≤ 1`, and either `K` is
algebraically closed, or `σ` is real and `K` is real closed. -/
theorem archimedeanHenselian : ArchimedeanHenselianStatement.{u} := by
  intro K _ h
  constructor
  · exact HenselianArchimedean.exists_of_isHenselianValuedField h
  · rintro ⟨σ, s, hs0, hs1, hσ, halg | ⟨hreal, hrc⟩⟩
    · have := halg
      exact HenselianIffSeparablyClosed.isHenselianValuedField_of_separableClosure_eq_bot
        HenselianArchimedean.separableClosure_eq_bot_of_isAlgClosed
    · have := hrc
      exact HenselianIffSeparablyClosed.isHenselianValuedField_of_separableClosure_eq_bot
        (HenselianArchimedean.separableClosure_eq_bot_of_isRealClosed σ hs0 hσ hreal)

end Langlands.AlgebraicGeometry.PointTopology
