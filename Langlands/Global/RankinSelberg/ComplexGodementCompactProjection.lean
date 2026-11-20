import Langlands.Representation.Archimedean.UnitaryFinitePolynomial
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact coefficient separation for Godement tests -/

noncomputable section

open MeasureTheory Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean.UnitaryFinitePolynomial
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "K" => Matrix.unitaryGroup (Fin n) ℂ

private theorem exists_separated_translate {v : K → ℂ} (hv : Continuous v)
    [FiniteDimensional ℂ (translateSpan v)] :
    ∃ (r : ℕ) (a b : Fin r → K → ℂ), (∀ j, Continuous (a j)) ∧ (∀ j, Continuous (b j)) ∧
      ∀ x k, v (x * k) = ∑ i, a i x * b i k := by
  let V := translateSpan v
  let B := Module.finBasis ℂ V
  choose ℓ hℓ using fun i => LinearMap.exists_extend (B.coord i)
  let a (i : Fin (Module.finrank ℂ V)) := (B i : K → ℂ)
  let b (i : Fin (Module.finrank ℂ V)) (k : K) := ℓ i (fun x => v (x * k))
  have hcont (f : K → ℂ) (hf : f ∈ V) : Continuous f := by
    induction hf using Submodule.span_induction with
    | mem f h =>
        obtain ⟨k, rfl⟩ := h
        exact hv.comp (continuous_mul_const k)
    | zero => exact continuous_const
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_smul c
  refine ⟨_, a, b, fun i => hcont _ (B i).2,
    fun i => continuous_functional_translate hv (ℓ i), fun x k => ?_⟩
  let u : V := ⟨fun y => v (y * k), translate_mem_translateSpan v k⟩
  have hs := congrArg (fun f : V => (f : K → ℂ) x) (B.sum_repr u)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← show (u : K → ℂ) x = v (x * k) from rfl, ← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrArg (fun f : V →ₗ[ℂ] ℂ => f u) (hℓ i)
  change ℓ i (u : K → ℂ) = _ at h
  rw [B.coord_apply] at h
  rw [mul_comm]
  exact congrArg (fun c : ℂ => a i x * c) h.symm

private theorem character_mul_star {T : Type*} [Group T] (χ : T →* ℂ) (hχnorm : ∀ t, ‖χ t‖ = 1)
    (t : T) : χ t * star (χ t) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχnorm t, one_pow, Complex.ofReal_one]

section Projection

variable {T : Type*} [Group T] [MeasurableSpace T]

private def torusProjection (η : Measure T) (e : T →* K) (χ : T →* ℂ) (v : K → ℂ) (x : K) : ℂ :=
  ∫ t : T, star (χ t) * v (x * e t) ∂η

variable [TopologicalSpace T] [IsTopologicalGroup T] [BorelSpace T] [CompactSpace T]
  [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (η : Measure T) [IsProbabilityMeasure η] [η.IsMulLeftInvariant]
  (e : T →* Matrix.unitaryGroup (Fin n) ℂ) (χ : T →* ℂ) (he : Continuous e) (hχ : Continuous χ)
  (hχnorm : ∀ t, ‖χ t‖ = 1)

omit [BorelSpace T] [IsTopologicalGroup T] [TopologicalSpace T] [CompactSpace T]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [η.IsMulLeftInvariant] in
include hχnorm in
private theorem projection_at_one {v : K → ℂ} (hv : ∀ t, v (e t) = χ t * v 1) :
    torusProjection η e χ v 1 = v 1 := by
  unfold torusProjection
  simp_rw [one_mul, hv, ← mul_assoc, mul_comm (star (χ _)) (χ _), character_mul_star χ hχnorm, one_mul]
  simp

omit [CompactSpace T] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [IsProbabilityMeasure η] in
include hχnorm in
private theorem projection_right_mul (v : K → ℂ) (x : K) (t : T) :
    torusProjection η e χ v (x * e t) = χ t * torusProjection η e χ v x := by
  unfold torusProjection
  rw [← integral_const_mul, ← integral_mul_left_eq_self (fun u : T => χ t * (star (χ u) * v (x * e u))) t]
  apply integral_congr_ae
  filter_upwards with u
  rw [map_mul, map_mul, star_mul', ← mul_assoc, ← mul_assoc, character_mul_star χ hχnorm,
    one_mul, mul_assoc x]

omit [IsTopologicalGroup T] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [η.IsMulLeftInvariant] in
include he hχ in
private theorem projection_expand {v : K → ℂ} (hv : Continuous v)
    [FiniteDimensional ℂ (translateSpan v)] :
    ∃ (r : ℕ) (a : Fin r → K → ℂ) (c : Fin r → ℂ), (∀ i, Continuous (a i)) ∧
      ∀ x, torusProjection η e χ v x = ∑ i, a i x * c i := by
  obtain ⟨r, a, b, ha, hb, hsum⟩ := exists_separated_translate hv
  let c (i : Fin r) := ∫ t, star (χ t) * b i (e t) ∂η
  refine ⟨r, a, c, ha, fun x => ?_⟩
  unfold torusProjection
  simp_rw [hsum, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  · intro i _
    exact ((continuous_star.comp hχ).mul (continuous_const.mul ((hb i).comp he))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit [IsTopologicalGroup T] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [η.IsMulLeftInvariant] in
include he hχ in
private theorem continuous_projection {v : K → ℂ} (hv : Continuous v)
    [FiniteDimensional ℂ (translateSpan v)] : Continuous (torusProjection η e χ v) := by
  obtain ⟨r, a, c, ha, h⟩ := projection_expand η e χ he hχ hv
  rw [funext h]
  exact continuous_finsetSum _ fun i _ => (ha i).mul continuous_const

omit [IsTopologicalGroup T] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [η.IsMulLeftInvariant] in
include he hχ in
private theorem finiteDimensional_star_inv_projection {v : K → ℂ} (hv : Continuous v)
    [FiniteDimensional ℂ (translateSpan v)] :
    FiniteDimensional ℂ (translateSpan (fun x => star (torusProjection η e χ v x⁻¹))) := by
  obtain ⟨r, a, b, ha, hb, hsum⟩ := exists_separated_translate hv
  let c (i : Fin r) (x : K) := star (∫ t, star (χ t) * b i (x⁻¹ * e t) ∂η)
  let V := Submodule.span ℂ (Set.range c)
  have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite _ (Set.finite_range c)
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  have h (x : K) : star (torusProjection η e χ v (x * k)⁻¹) =
      ∑ i, star (a i k⁻¹) * c i x := by
    unfold torusProjection
    simp only [_root_.mul_inv_rev, mul_assoc]
    simp_rw [hsum k⁻¹, Finset.mul_sum]
    rw [integral_finsetSum, star_sum]
    · apply Finset.sum_congr rfl
      intro i _
      have heq : (∫ t, star (χ t) * (a i k⁻¹ * b i (x⁻¹ * e t)) ∂η) =
          a i k⁻¹ * ∫ t, star (χ t) * b i (x⁻¹ * e t) ∂η := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        ring
      rw [heq, star_mul']
    · intro i _
      exact ((continuous_star.comp hχ).mul (continuous_const.mul
        ((hb i).comp (continuous_const.mul he)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have heq : (fun x => star (torusProjection η e χ v (x * k)⁻¹)) =
      ∑ i, star (a i k⁻¹) • c i := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h x
  change (fun x => star (torusProjection η e χ v (x * k)⁻¹)) ∈ V
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

include he hχ hχnorm in
private theorem pairing_projection {v : K → ℂ} (hv : Continuous v)
    [FiniteDimensional ℂ (translateSpan v)] (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsMulRightInvariant] :
    (∫ x, torusProjection η e χ v x * star (torusProjection η e χ v x) ∂μ) =
      ∫ x, v x * star (torusProjection η e χ v x) ∂μ := by
  let A := torusProjection η e χ v
  have hA : Continuous A := continuous_projection η e χ he hχ hv
  let B (x : K) (t : T) := star (χ t) * v (x * e t) * star (A x)
  have hB : Continuous (Function.uncurry B) := by
    exact (((continuous_star.comp hχ).comp continuous_snd).mul
      (hv.comp (continuous_fst.mul (he.comp continuous_snd)))).mul
        ((continuous_star.comp hA).comp continuous_fst)
  have hswap := integral_integral_swap_of_hasCompactSupport hB (HasCompactSupport.of_compactSpace _)
    (μ := μ) (ν := η)
  calc
    _ = ∫ x, ∫ t, B x t ∂η ∂μ := by simp only [B, integral_mul_const, A, torusProjection]
    _ = ∫ t, ∫ x, B x t ∂μ ∂η := hswap
    _ = _ := by
      have h (t : T) : (∫ x, B x t ∂μ) = ∫ x, v x * star (A x) ∂μ := by
        rw [← integral_mul_right_eq_self (fun x => v x * star (A x)) (e t)]
        apply integral_congr_ae
        filter_upwards with x
        change B x t = v (x * e t) * star (A (x * e t))
        rw [show A (x * e t) = χ t * A x from projection_right_mul η e χ hχnorm v x t, star_mul']
        unfold B
        ring
      simp only [h, integral_const, probReal_univ, one_smul, A]

/-- A compact-finite function with nonzero value at one and the given torus covariance at one
admits a compact-finite coefficient of the same left torus weight that separates it. -/
def ComplexGodementCompactProjectionStatement : Prop :=
  ∀ (η : Measure T) [IsProbabilityMeasure η] [η.IsMulLeftInvariant]
    (e : T →* K) (χ : T →* ℂ), Continuous e → Continuous χ → (∀ t, ‖χ t‖ = 1) →
    ∀ (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (v : K → ℂ),
      Continuous v → FiniteDimensional ℂ (translateSpan v) →
      (∀ t, v (e t) = χ t * v 1) → v 1 ≠ 0 →
      ∃ g : K → ℂ, Continuous g ∧ FiniteDimensional ℂ (translateSpan g) ∧
        (∀ t x, g (e t * x) = χ t * g x) ∧ 0 < (∫ x, v x * g x⁻¹ ∂μ).re

theorem complexGodementCompactProjection : ComplexGodementCompactProjectionStatement (n := n) (T := T) := by
  intro η hηp hηi e χ he hχ hχn μ hμ hμr v hv hfin hcov hv₁
  let : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  let : FiniteDimensional ℂ (translateSpan v) := hfin
  let A := torusProjection η e χ v
  let g := fun x : K => star (A x⁻¹)
  have hA : Continuous A := continuous_projection η e χ he hχ hv
  refine ⟨g, continuous_star.comp (hA.comp continuous_inv),
    finiteDimensional_star_inv_projection η e χ he hχ hv, ?_, ?_⟩
  · intro t x
    have heq : A x⁻¹ = χ t * A (e t * x)⁻¹ := by
      have h := projection_right_mul η e χ hχn v (e t * x)⁻¹ t
      simpa only [_root_.mul_inv_rev, inv_mul_cancel_right] using h
    have hstar := congrArg (starRingEnd ℂ) heq
    change star (A x⁻¹) = star (χ t * A (e t * x)⁻¹) at hstar
    rw [star_mul'] at hstar
    change star (A (e t * x)⁻¹) = χ t * star (A x⁻¹)
    rw [hstar, ← mul_assoc, character_mul_star χ hχn, one_mul]
  · simp only [g, inv_inv]
    rw [← pairing_projection η e χ he hχ hχn hv μ]
    have hNorm : (fun x => torusProjection η e χ v x * star (torusProjection η e χ v x)) =
        fun x => ((‖A x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      change A x * star (A x) = ((‖A x‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hNorm, integral_complex_ofReal, Complex.ofReal_re]
    refine (hA.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => sq_nonneg _) (x := 1) ?_
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (by simpa only [A, projection_at_one η e χ hχn hcov]))

end Projection

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
