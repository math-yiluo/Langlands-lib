import Langlands.Shimura.Unitary.PositiveRationalTwistStatement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-! # Existence of a rational positive skew twist -/

noncomputable section

universe u v w

open scoped TensorProduct Topology
open Filter

namespace Langlands.Shimura.AlgebraInvolution

section BaseChange

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Ring A] [Algebra R A]

/-- Scalar extension of a skew-conjugated involution is conjugation by the
extended unit. -/
theorem baseChange_skewAdjoint_apply (σ : AlgebraInvolution R A) (β : Aˣ)
    (hβ : σ (β : A) = -(β : A)) (x : S ⊗[R] A) :
    (σ.skewAdjoint β hβ).baseChange S x =
      ((1 : S) ⊗ₜ[R] (β : A)) * σ.baseChange S x * ((1 : S) ⊗ₜ[R] (↑β⁻¹ : A)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [apply_add, hx, hy, mul_add, add_mul]
  | tmul s a => simp [Algebra.TensorProduct.tmul_mul_tmul]

end BaseChange

section Real

variable {B : Type*} [Ring B] [Algebra ℝ B] {τ : AlgebraInvolution ℝ B}

/-- A positive complex homomorphism `h` supplies the real skew element `h(-i)`,
for which `y ↦ tr(-(h(-i) τ(y) h(-i) y))` is positive on nonzero elements. -/
theorem PositiveComplexHom.exists_skew_trace_pos (h : PositiveComplexHom τ) :
    ∃ v : B, τ v = -v ∧ ∀ y : B, y ≠ 0 →
      0 < LinearMap.trace ℝ B (LinearMap.mulLeft ℝ (-(v * τ y * v * y))) := by
  set v := h.val.hom (-Complex.I) with hv
  have hI : h.val.hom Complex.I = -v := by
    rw [hv, _root_.map_neg, neg_neg]
  have hτv : τ v = -v := by
    rw [hv, h.val.star_compatible, star_neg, Complex.star_def, Complex.conj_I, neg_neg, hI]
  have hvv : v * v = -1 := by
    have h1 : h.val.hom Complex.I * v = 1 := h.val.hom_I_mul_hom_neg_I
    rw [hI, neg_mul] at h1
    rw [← neg_neg (v * v), h1]
  refine ⟨v, hτv, fun y hy => ?_⟩
  have hx : v * y ≠ 0 := by
    intro h0
    apply hy
    calc y = -(v * v) * y := by rw [hvv, neg_neg, one_mul]
      _ = 0 := by rw [neg_mul, mul_assoc, h0, mul_zero, neg_zero]
  have key := h.property (v * y) hx
  have htw : h.val.twist (v * y) * (v * y) = -(v * τ y * v * y) := by
    rw [ComplexHom.twist_apply, τ.apply_mul, hτv, ← hv, hI]
    calc v * (τ y * -v) * -v * (v * y) = v * τ y * v * (v * v) * y := by
          simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(v * τ y * v * y) := by
          rw [hvv]
          simp only [mul_neg, neg_mul, mul_one, mul_assoc]
  rwa [htw] at key

end Real

section Rational

variable {A : Type*} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A)

/-- A rational skew element whose skew trace form on the real scalar extension is
positive is a unit, and conjugating the involution by it gives a positive
involution on the real scalar extension. -/
theorem exists_isPositive_skewAdjoint_of_trace_pos [FiniteDimensional ℚ A] (a : A)
    (ha : σ a = -a)
    (hpos : ∀ y : ℝ ⊗[ℚ] A, y ≠ 0 → 0 < LinearMap.trace ℝ (ℝ ⊗[ℚ] A)
      (LinearMap.mulLeft ℝ
        (-(((1 : ℝ) ⊗ₜ[ℚ] a) * σ.baseChange ℝ y * ((1 : ℝ) ⊗ₜ[ℚ] a) * y)))) :
    ∃ β : Aˣ, ∃ hβ : σ (β : A) = -(β : A), ((σ.skewAdjoint β hβ).baseChange ℝ).IsPositive := by
  have hinj : Function.Injective (fun c : A => (1 : ℝ) ⊗ₜ[ℚ] c) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℝ).injective
  have hunit : IsUnit a := by
    have hmul : Function.Injective (LinearMap.mulLeft ℚ a) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      rw [LinearMap.mulLeft_apply] at hc
      by_contra hc0
      have hy : (1 : ℝ) ⊗ₜ[ℚ] c ≠ 0 := fun h0 =>
        hc0 (hinj (h0.trans (TensorProduct.tmul_zero A (1 : ℝ)).symm))
      have h := hpos _ hy
      simp only [baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc, hc,
        mul_zero, TensorProduct.tmul_zero, neg_zero, LinearMap.mulLeft_zero_eq_zero,
        map_zero, lt_irrefl] at h
    exact IsUnit.isUnit_iff_mulLeft_bijective.mpr
      ⟨hmul, LinearMap.injective_iff_surjective.mp hmul⟩
  have hβ : σ (hunit.unit : A) = -(hunit.unit : A) := by
    rw [hunit.unit_spec]
    exact ha
  refine ⟨hunit.unit, hβ, fun x hx => ?_⟩
  set b : ℝ ⊗[ℚ] A := (1 : ℝ) ⊗ₜ[ℚ] a with hb
  set b' : ℝ ⊗[ℚ] A := (1 : ℝ) ⊗ₜ[ℚ] (↑hunit.unit⁻¹ : A) with hb'
  have hb'b : b' * b = 1 := by
    rw [hb, hb', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hunit.val_inv_mul,
      Algebra.TensorProduct.one_def]
  have hbb' : b * b' = 1 := by
    rw [hb, hb', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hunit.mul_val_inv,
      Algebra.TensorProduct.one_def]
  have hρb : σ.baseChange ℝ b = -b := by
    rw [hb, baseChange_tmul, ha, TensorProduct.tmul_neg]
  obtain ⟨y, rfl⟩ : ∃ y, x = b * y := ⟨b' * x, by rw [← mul_assoc, hbb', one_mul]⟩
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (mul_zero b)
  have h := hpos y hy
  rw [baseChange_skewAdjoint_apply, hunit.unit_spec, apply_mul, hρb]
  have hcalc : b * (σ.baseChange ℝ y * -b) * b' * (b * y) =
      -(b * σ.baseChange ℝ y * b * y) := by
    calc b * (σ.baseChange ℝ y * -b) * b' * (b * y) =
        -(b * σ.baseChange ℝ y * b * (b' * b) * y) := by
          simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(b * σ.baseChange ℝ y * b * y) := by rw [hb'b, mul_one]
  rw [hcalc]
  exact h

/-- Openness and density: a real skew element with positive skew trace form can
be replaced by a rational skew element with the same positivity. -/
theorem exists_rational_skew_trace_pos [FiniteDimensional ℚ A] (v₀ : ℝ ⊗[ℚ] A)
    (hv₀ : σ.baseChange ℝ v₀ = -v₀)
    (hpos : ∀ y : ℝ ⊗[ℚ] A, y ≠ 0 → 0 < LinearMap.trace ℝ (ℝ ⊗[ℚ] A)
      (LinearMap.mulLeft ℝ (-(v₀ * σ.baseChange ℝ y * v₀ * y)))) :
    ∃ a : A, σ a = -a ∧ ∀ y : ℝ ⊗[ℚ] A, y ≠ 0 → 0 < LinearMap.trace ℝ (ℝ ⊗[ℚ] A)
      (LinearMap.mulLeft ℝ
        (-(((1 : ℝ) ⊗ₜ[ℚ] a) * σ.baseChange ℝ y * ((1 : ℝ) ⊗ₜ[ℚ] a) * y))) := by
  let _ : TopologicalSpace (ℝ ⊗[ℚ] A) := moduleTopology ℝ (ℝ ⊗[ℚ] A)
  have : IsModuleTopology ℝ (ℝ ⊗[ℚ] A) := ⟨rfl⟩
  have : IsTopologicalRing (ℝ ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing ℝ (ℝ ⊗[ℚ] A)
  set ρ := σ.baseChange ℝ with hρ
  -- The regular trace, as a continuous linear functional.
  let T : ℝ ⊗[ℚ] A →ₗ[ℝ] ℝ := (LinearMap.trace ℝ (ℝ ⊗[ℚ] A)).comp (LinearMap.mul ℝ _)
  have hTapp (z : ℝ ⊗[ℚ] A) :
      T z = LinearMap.trace ℝ (ℝ ⊗[ℚ] A) (LinearMap.mulLeft ℝ z) := by
    simp only [T, LinearMap.comp_apply]
    congr 1
  have hTc : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hρc : Continuous fun z : ℝ ⊗[ℚ] A => ρ z :=
    IsModuleTopology.continuous_of_linearMap ρ.linear
  let F : (ℝ ⊗[ℚ] A) × (ℝ ⊗[ℚ] A) → ℝ := fun p => T (-(p.1 * ρ p.2 * p.1 * p.2))
  have hFc : Continuous F :=
    hTc.comp ((((continuous_fst.mul (hρc.comp continuous_snd)).mul continuous_fst).mul
      continuous_snd).neg)
  -- Coordinates from a rational basis.
  let bA := Module.finBasis ℚ A
  let bV := Algebra.TensorProduct.basis ℝ bA
  let Φ : (Fin (Module.finrank ℚ A) → ℝ) ≃ₗ[ℝ] ℝ ⊗[ℚ] A := bV.equivFun.symm
  have hΦc : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ.toLinearMap
  -- The image of the unit sphere is compact and avoids zero.
  let S := Φ '' Metric.sphere 0 1
  have hS : IsCompact S := (isCompact_sphere 0 1).image hΦc
  have hS0 : ∀ k ∈ S, k ≠ 0 := by
    rintro _ ⟨c, hc, rfl⟩ h0
    have hc0 : c = 0 := Φ.injective (h0.trans Φ.map_zero.symm)
    rw [hc0, mem_sphere_zero_iff_norm, norm_zero] at hc
    exact zero_ne_one hc
  -- Positivity on the compact set persists near `v₀`.
  have hev : ∀ᶠ v in 𝓝 v₀, ∀ k ∈ S, 0 < F (v, k) :=
    hS.eventually_forall_of_forall_eventually fun k hk =>
      (hFc.tendsto (v₀, k)).eventually (lt_mem_nhds (by show 0 < T _; rw [hTapp]; exact hpos k (hS0 k hk)))
  -- The skew projection fixes `v₀`.
  let s : ℝ ⊗[ℚ] A →ₗ[ℝ] ℝ ⊗[ℚ] A := (1 / 2 : ℝ) • (LinearMap.id - ρ.linear)
  have hsapp (z : ℝ ⊗[ℚ] A) : s z = (1 / 2 : ℝ) • (z - ρ z) := rfl
  have hsc : Continuous s := IsModuleTopology.continuous_of_linearMap s
  have hsv₀ : s v₀ = v₀ := by
    rw [hsapp, hv₀, sub_neg_eq_add, ← two_smul ℝ v₀, smul_smul]
    norm_num
  have hev' : ∀ᶠ w in 𝓝 v₀, ∀ k ∈ S, 0 < F (s w, k) := by
    have h := hsc.tendsto v₀
    rw [hsv₀] at h
    exact h.eventually hev
  -- Rational elements are dense in the real scalar extension.
  have hdense : Dense (Set.range fun c : A => (1 : ℝ) ⊗ₜ[ℚ] c) := by
    have h1 : DenseRange (Φ ∘ Pi.map fun _ => ((↑) : ℚ → ℝ)) :=
      Φ.surjective.denseRange.comp (DenseRange.piMap fun _ => Rat.denseRange_cast) hΦc
    refine h1.mono ?_
    rintro _ ⟨r, rfl⟩
    refine ⟨∑ i, r i • bA i, ?_⟩
    simp only [Function.comp_apply, Φ, Module.Basis.equivFun_symm_apply, Pi.map_apply,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_repr_symm_apply', ← TensorProduct.smul_tmul,
      Rat.smul_one_eq_cast]
  obtain ⟨_, hw, ⟨a, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense v₀) _ hev'
  refine ⟨(1 / 2 : ℚ) • (a - σ a), ?_, ?_⟩
  · rw [map_smul, map_sub, σ.involutive a, ← smul_neg, neg_sub]
  · have hsa : s ((1 : ℝ) ⊗ₜ[ℚ] a) = (1 : ℝ) ⊗ₜ[ℚ] ((1 / 2 : ℚ) • (a - σ a)) := by
      rw [hsapp, hρ, baseChange_tmul, ← TensorProduct.tmul_sub, TensorProduct.smul_tmul',
        ← TensorProduct.smul_tmul, Rat.smul_one_eq_cast]
      norm_num
    have hw' : ∀ k ∈ S, 0 < F (s ((1 : ℝ) ⊗ₜ[ℚ] a), k) := hw
    rw [hsa] at hw'
    intro y hy
    set c := Φ.symm y with hc
    have hc0 : c ≠ 0 := fun h0 => hy (by rw [← Φ.apply_symm_apply y, ← hc, h0, map_zero])
    set t := ‖c‖ with ht
    have ht0 : 0 < t := norm_pos_iff.mpr hc0
    have hk : Φ (t⁻¹ • c) ∈ S := by
      refine ⟨t⁻¹ • c, ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0,
        ← ht, inv_mul_cancel₀ ht0.ne']
    have hyk : y = t • Φ (t⁻¹ • c) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, hc, Φ.apply_symm_apply]
    have hF : 0 < F ((1 : ℝ) ⊗ₜ[ℚ] ((1 / 2 : ℚ) • (a - σ a)), Φ (t⁻¹ • c)) := hw' _ hk
    rw [hyk, ← hTapp]
    have hscale (b k : ℝ ⊗[ℚ] A) :
        -(b * ρ (t • k) * b * (t • k)) = (t * t) • -(b * ρ k * b * k) := by
      rw [apply_smul]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_neg]
    rw [hscale, map_smul, smul_eq_mul]
    exact mul_pos (mul_pos ht0 ht0) hF

end Rational

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}

/-- The actual Harris algebra has a rational skew unit whose conjugated
involution is positive on the real scalar extension. -/
theorem positiveRationalSkewTwistExists (D : CentralSimpleUnitaryData E K A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ) :
    D.PositiveRationalSkewTwistExists C := by
  have : FiniteDimensional K A := D.finite
  have : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  have : FiniteDimensional E A := Module.Finite.of_restrictScalars_finite ℚ E A
  obtain ⟨v₀, hv₀, hpos⟩ :=
    (C.realPositiveComplexHom (Module.finBasis E A)).exists_skew_trace_pos
  obtain ⟨a, ha, hapos⟩ :=
    D.toSecondKindInvolution.rationalInvolution.exists_rational_skew_trace_pos v₀ hv₀ hpos
  exact D.toSecondKindInvolution.rationalInvolution.exists_isPositive_skewAdjoint_of_trace_pos
    a ha hapos

end Langlands.Shimura.CentralSimpleUnitaryData
