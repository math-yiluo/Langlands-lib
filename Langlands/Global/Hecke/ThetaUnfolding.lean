import Langlands.Global.Hecke.AdelicPoisson

/-!
# Unfolding theta integrals over the fundamental cone

Let `K` be a number field, `V = mixedSpace K` its mixed space with norm `N`, `C` Mathlib's
fundamental cone for the action of the units, and `θ(a, F)(y) = ∑_{γ ∈ K} a(γ) F(γ y)`. For a
weight `χ` on `V`, multiplicative on points of nonzero norm, and coefficients `a` transforming
under the units like `χ`, this module unfolds the Mellin integral of `θ(a, F) - a(0) F(0)` over
the cone into an Euler-type sum over the orbits of the units on `Kˣ`
(`integral_thetaSeries_unfold`):

`∫_C (θ(a, F)(x) - a(0) F(0)) χ(x) N(x)^(s-1) dx
  = w ∑_p a(γ_p) χ(γ_p)⁻¹ N(γ_p)^(-s) ∫_V F χ N^(s-1)`,

`γ_p` representatives of the orbits and `w` the number of roots of unity, and similarly the dual
integral `∫_C (θ(b, G)(x⁻¹) - b(0) G(0)) χ(x) N(x)^(-s-1) dx`
(`integral_thetaSeries_inv_unfold`). It also provides the changes of variables under
multiplication and under inversion needed for this (`integrable_comp_mul_left_iff`,
`integrable_comp_inv_iff`, `integral_inv_eq_and_integrable`).
-/

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Module Filter
open scoped nonZeroDivisors Classical

namespace Langlands.Global.Hecke

variable {K : Type*} [Field K] [NumberField K]

instance : Countable Kˣ :=
  Function.Injective.countable (f := (Units.val : Kˣ → K)) (fun _ _ h => Units.ext h)

/-! ### Change of variables -/

section ChangeOfVariables

theorem integrable_comp_mul_left_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) (f : mixedSpace K → E) :
    Integrable (fun x => f (y * x)) ↔ Integrable f := by
  have h := integrable_map_equiv (μ := volume) (mulHomeomorph hy).toMeasurableEquiv f
  have hpos : 0 < (mixedEmbedding.norm y)⁻¹ :=
    inv_pos.mpr (lt_of_le_of_ne (mixedEmbedding.norm_nonneg y) (Ne.symm hy))
  rw [map_mulHomeomorph_volume hy, integrable_smul_measure (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top] at h
  exact h.symm

theorem norm_mixedEmbedding_units_ne_zero (γ : Kˣ) :
    mixedEmbedding.norm (mixedEmbedding K (γ : K)) ≠ 0 := by
  rw [norm_eq_norm]
  exact Rat.cast_ne_zero.mpr (abs_ne_zero.mpr ((Algebra.norm_ne_zero_iff (R := ℚ)).mpr γ.ne_zero))

theorem norm_mixedEmbedding_units_pos (γ : Kˣ) :
    0 < mixedEmbedding.norm (mixedEmbedding K (γ : K)) :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm (norm_mixedEmbedding_units_ne_zero γ))

omit [NumberField K] in
theorem mixedSpace_inv_zero : (0 : mixedSpace K)⁻¹ = 0 := by
  ext w <;> simp

omit [NumberField K] in
/-- The mixed embedding commutes with inversion. -/
theorem mixedEmbedding_inv (μ : K) : mixedEmbedding K μ⁻¹ = (mixedEmbedding K μ)⁻¹ := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [inv_zero (G₀ := K), map_zero, mixedSpace_inv_zero]
  · refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, mul_inv_cancel₀ hμ, map_one]

omit [NumberField K] in
theorem coe_units_inv (u : (𝓞 K)ˣ) :
    (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = (((u : 𝓞 K) : K))⁻¹ :=
  map_units_inv (algebraMap (𝓞 K) K) u

/-- Integrability under the componentwise inversion `x ↦ x⁻¹`, whose Jacobian has absolute
value `N(x)⁻²`. -/
theorem integrable_comp_inv_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : mixedSpace K → E) :
    Integrable (fun x => (mixedEmbedding.norm x)⁻¹ ^ 2 • g x⁻¹) ↔ Integrable g := by
  set U := {x : mixedSpace K | mixedEmbedding.norm x ≠ 0}
  have himage : (fun y : mixedSpace K => y⁻¹) '' U = U := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, U]
    refine ⟨?_, fun hx => ⟨x⁻¹, by rw [norm_inv']; exact inv_ne_zero hx, inv_inv x⟩⟩
    rintro ⟨y, hy, rfl⟩
    rw [norm_inv']
    exact inv_ne_zero hy
  have hinj : Set.InjOn (fun y : mixedSpace K => y⁻¹) U := fun a _ b _ h => inv_injective h
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_setOf_norm_ne_zero (f := fun y : mixedSpace K => y⁻¹)
    (f' := fun x => mulL (-(x⁻¹ * x⁻¹))) (fun x hx => (hasFDerivAt_inv' hx).hasFDerivWithinAt)
    hinj g
  rw [himage] at h
  have hU : ∀ f : mixedSpace K → E, IntegrableOn f U ↔ Integrable f := fun f => by
    rw [← integrableOn_univ]
    exact integrableOn_congr_set_ae setOf_norm_ne_zero_ae_eq_univ
  rw [← hU, ← hU, h]
  refine integrableOn_congr_fun (fun x _ => ?_) measurableSet_setOf_norm_ne_zero
  rw [abs_det_mulL, norm_neg', map_mul, norm_inv', sq]

/-- `∫ G(y⁻¹) χ(y) N(y)^(-s-1) dy = ∫ G(y) χ(y⁻¹) N(y)^(s-1) dy`, with the corresponding
integrability. -/
theorem integral_inv_eq_and_integrable (G χ : mixedSpace K → ℂ) (s : ℂ) :
    (Integrable (fun y => G y⁻¹ * χ y * (mixedEmbedding.norm y : ℂ) ^ (-s - 1)) ↔
        Integrable (fun y => G y * χ y⁻¹ * (mixedEmbedding.norm y : ℂ) ^ (s - 1))) ∧
      ∫ y, G y⁻¹ * χ y * (mixedEmbedding.norm y : ℂ) ^ (-s - 1) =
        ∫ y, G y * χ y⁻¹ * (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
  set g := fun y : mixedSpace K => G y⁻¹ * χ y * (mixedEmbedding.norm y : ℂ) ^ (-s - 1)
  have hpt : (fun x => (mixedEmbedding.norm x)⁻¹ ^ 2 • g x⁻¹) =ᵐ[volume]
      fun y => G y * χ y⁻¹ * (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
    filter_upwards [ae_norm_ne_zero] with x hx
    have hxpos : 0 < mixedEmbedding.norm x :=
      lt_of_le_of_ne (mixedEmbedding.norm_nonneg x) (Ne.symm hx)
    have hx' : (mixedEmbedding.norm x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [g, inv_inv, norm_inv', Complex.real_smul]
    rw [ofReal_inv_cpow_of_nonneg hxpos.le]
    have h2 : (mixedEmbedding.norm x : ℂ) ^ (-(-s - 1)) =
        (mixedEmbedding.norm x : ℂ) ^ (s - 1) * (mixedEmbedding.norm x : ℂ) ^ 2 := by
      rw [show -(-s - 1) = (s - 1) + (2 : ℕ) by push_cast; ring,
        Complex.cpow_add _ _ hx', Complex.cpow_natCast]
    rw [h2]
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← integrable_comp_inv_iff g]
    exact integrable_congr hpt
  · rw [← integral_comp_inv g]
    exact integral_congr_ae hpt

end ChangeOfVariables

/-! ### Unfolding -/

section Unfolding

variable {χ : mixedSpace K → ℂ}
  (hχmul : ∀ x y, mixedEmbedding.norm x ≠ 0 → mixedEmbedding.norm y ≠ 0 →
    χ (x * y) = χ x * χ y)
  (hχ1 : χ 1 = 1)

include hχmul hχ1 in
theorem ne_zero_of_multiplicative {c : mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0) :
    χ c ≠ 0 := by
  intro h0
  have hinv : mixedEmbedding.norm c⁻¹ ≠ 0 := by
    rw [norm_inv']
    exact inv_ne_zero hc
  have h1 := hχmul c c⁻¹ hc hinv
  rw [mul_inv_cancel_of_norm_ne_zero hc, hχ1, h0, zero_mul] at h1
  exact one_ne_zero h1

/-- The integrand `y ↦ a(γ) F(γ y) χ(y) N(y)^(s-1)` of the unfolded theta integral. -/
def unfoldIntegrand (a : K → ℂ) (F χ : mixedSpace K → ℂ) (s : ℂ) (γ : K) (y : mixedSpace K) :
    ℂ :=
  a γ * F (mixedEmbedding K γ * y) * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)

include hχmul hχ1 in
/-- Pointwise change of variables `y ↦ c y`, `c = ι γ`. -/
theorem unfoldIntegrand_eq (a : K → ℂ) (F : mixedSpace K → ℂ) (s : ℂ) (γ : Kˣ)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    unfoldIntegrand a F χ s γ y =
      a γ * (χ (mixedEmbedding K (γ : K)))⁻¹ *
        (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (1 - s) *
          (F (mixedEmbedding K (γ : K) * y) * χ (mixedEmbedding K (γ : K) * y) *
            (mixedEmbedding.norm (mixedEmbedding K (γ : K) * y) : ℂ) ^ (s - 1)) := by
  have hc := norm_mixedEmbedding_units_ne_zero γ
  have hcpos := norm_mixedEmbedding_units_pos γ
  have hχc := ne_zero_of_multiplicative hχmul hχ1 hc
  rw [unfoldIntegrand]
  generalize mixedEmbedding K (γ : K) = c at hc hcpos hχc ⊢
  rw [hχmul c y hc hy, map_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hcpos.le (mixedEmbedding.norm_nonneg y)]
  have hcc : (mixedEmbedding.norm c : ℂ) ^ (1 - s) * (mixedEmbedding.norm c : ℂ) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hc)]
    simp
  calc _ = a γ * F (c * y) * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1) * ((χ c)⁻¹ * χ c) *
        ((mixedEmbedding.norm c : ℂ) ^ (1 - s) * (mixedEmbedding.norm c : ℂ) ^ (s - 1)) := by
        rw [inv_mul_cancel₀ hχc, hcc]
        ring
    _ = _ := by ring

include hχmul hχ1 in
theorem integrable_unfoldIntegrand {a : K → ℂ} {F : mixedSpace K → ℂ} {s : ℂ}
    (hint : Integrable fun y => F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) (γ : Kˣ) :
    Integrable (unfoldIntegrand a F χ s γ) := by
  have hc := norm_mixedEmbedding_units_ne_zero γ
  have h1 := ((integrable_comp_mul_left_iff hc _).mpr hint).const_mul
    (a γ * (χ (mixedEmbedding K (γ : K)))⁻¹ *
      (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (1 - s))
  refine h1.congr ?_
  filter_upwards [ae_norm_ne_zero] with y hy
  exact (unfoldIntegrand_eq hχmul hχ1 a F s γ hy).symm

include hχmul hχ1 in
/-- `∫ a(γ) F(γ y) χ(y) N(y)^(s-1) dy = a(γ) χ(γ)⁻¹ N(γ)^(-s) ∫ F χ N^(s-1)`. -/
theorem integral_unfoldIntegrand (a : K → ℂ) (F : mixedSpace K → ℂ) (s : ℂ) (γ : Kˣ) :
    ∫ y, unfoldIntegrand a F χ s γ y =
      a γ * (χ (mixedEmbedding K (γ : K)))⁻¹ *
        (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (-s) *
          ∫ y, F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
  have hc := norm_mixedEmbedding_units_ne_zero γ
  have hc' : (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc
  rw [integral_congr_ae (g := fun y => (a γ * (χ (mixedEmbedding K (γ : K)))⁻¹ *
      (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (1 - s)) *
        (F (mixedEmbedding K (γ : K) * y) * χ (mixedEmbedding K (γ : K) * y) *
          (mixedEmbedding.norm (mixedEmbedding K (γ : K) * y) : ℂ) ^ (s - 1)))
      (by filter_upwards [ae_norm_ne_zero] with y hy
          exact unfoldIntegrand_eq hχmul hχ1 a F s γ hy),
    integral_const_mul, integral_comp_mul_left hc
      (fun y => F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)), Complex.real_smul]
  have hk : (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (1 - s) *
      (((mixedEmbedding.norm (mixedEmbedding K (γ : K)))⁻¹ : ℝ) : ℂ) =
        (mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hc', Complex.cpow_one, Complex.ofReal_inv]
    field_simp
  rw [← hk]
  ring

include hχmul hχ1 in
/-- The integral of the norm of the unfolded integrand. -/
theorem integral_norm_unfoldIntegrand (a : K → ℂ) (F : mixedSpace K → ℂ) (s : ℂ) (γ : Kˣ) :
    ∫ y, ‖unfoldIntegrand a F χ s γ y‖ =
      ‖a γ‖ * ‖χ (mixedEmbedding K (γ : K))‖⁻¹ *
        mixedEmbedding.norm (mixedEmbedding K (γ : K)) ^ (-s.re) *
          ∫ y, ‖F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)‖ := by
  have hc := norm_mixedEmbedding_units_ne_zero γ
  have hcpos := norm_mixedEmbedding_units_pos γ
  rw [integral_congr_ae (g := fun y => (‖a γ‖ * ‖χ (mixedEmbedding K (γ : K))‖⁻¹ *
      mixedEmbedding.norm (mixedEmbedding K (γ : K)) ^ (1 - s.re)) *
        ‖F (mixedEmbedding K (γ : K) * y) * χ (mixedEmbedding K (γ : K) * y) *
          (mixedEmbedding.norm (mixedEmbedding K (γ : K) * y) : ℂ) ^ (s - 1)‖)
      (by filter_upwards [ae_norm_ne_zero] with y hy
          rw [unfoldIntegrand_eq hχmul hχ1 a F s γ hy, norm_mul, norm_mul, norm_mul, norm_inv,
            Complex.norm_cpow_eq_rpow_re_of_pos hcpos, Complex.sub_re, Complex.one_re]),
    integral_const_mul, integral_comp_mul_left hc
      (fun y => ‖F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)‖), smul_eq_mul]
  have hk : mixedEmbedding.norm (mixedEmbedding K (γ : K)) ^ (1 - s.re) *
      (mixedEmbedding.norm (mixedEmbedding K (γ : K)))⁻¹ =
        mixedEmbedding.norm (mixedEmbedding K (γ : K)) ^ (-s.re) := by
    rw [Real.rpow_sub hcpos, Real.rpow_one, Real.rpow_neg hcpos.le]
    field_simp
  rw [← hk]
  ring

include hχmul in
/-- The unfolded integrand transforms under the units through the unit action. -/
theorem unfoldIntegrand_units_mul {a : K → ℂ}
    (hunit : ∀ (u : (𝓞 K)ˣ) (γ : K),
      a (((u : 𝓞 K) : K) * γ) = χ (mixedEmbedding K ((u : 𝓞 K) : K)) * a γ)
    (F : mixedSpace K → ℂ) (s : ℂ) (u : (𝓞 K)ˣ) (γ : K) {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    unfoldIntegrand a F χ s (((u : 𝓞 K) : K) * γ) x = unfoldIntegrand a F χ s γ (u • x) := by
  have hu := norm_mixedEmbedding_unit_ne_zero u
  have hF : mixedEmbedding K (((u : 𝓞 K) : K) * γ) * x =
      mixedEmbedding K γ * (mixedEmbedding K ((u : 𝓞 K) : K) * x) := by
    rw [map_mul]
    ring
  rw [unfoldIntegrand, unfoldIntegrand, hunit, hF, unit_smul_eq_mul, hχmul _ _ hu hx,
    map_mul mixedEmbedding.norm, norm_unit, one_mul]
  ring

include hχmul hχ1 in
/-- **Unfolding the theta integral over the fundamental cone.** Let `a` transform under the units
like `χ` (`a(u γ) = χ(u) a(γ)`), let `χ` be multiplicative on points of nonzero norm with
`χ(1) = 1`, and let `γ ↦ a(γ) F(γ x)` be summable over `K` at every point `x` of the cone. Let
`gen p` be representatives of the orbits of the units on `Kˣ`, indexed by `P`, i.e.
`P × (𝓞 K)ˣ ≃ Kˣ, (p, u) ↦ u · gen p`. If `∑_p |a(gen p)| |χ(gen p)|⁻¹ N(gen p)^(-Re s)`
converges and `F χ N^(s-1)` is integrable, then
`∫_C (θ(a, F)(x) - a(0) F(0)) χ(x) N(x)^(s-1) dx
  = w ∑_p a(gen p) χ(gen p)⁻¹ N(gen p)^(-s) ∫_V F χ N^(s-1)`,
`w` the number of roots of unity. -/
theorem integral_thetaSeries_unfold_of_summable {P : Type*} (gen : P → Kˣ)
    (e : P × (𝓞 K)ˣ ≃ Kˣ) (he : ∀ p u, ((e (p, u) : Kˣ) : K) = ((u : 𝓞 K) : K) * (gen p : K))
    {a : K → ℂ}
    (hunit : ∀ (u : (𝓞 K)ˣ) (γ : K),
      a (((u : 𝓞 K) : K) * γ) = χ (mixedEmbedding K ((u : 𝓞 K) : K)) * a γ)
    {F : mixedSpace K → ℂ}
    (hS : ∀ x ∈ fundamentalCone K, Summable fun γ : K => a γ * F (mixedEmbedding K γ * x))
    (s : ℂ)
    (hsum : Summable fun p => ‖a (gen p)‖ * ‖χ (mixedEmbedding K (gen p : K))‖⁻¹ *
      mixedEmbedding.norm (mixedEmbedding K (gen p : K)) ^ (-s.re))
    (hint : Integrable fun y => F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) :
    ∫ x in fundamentalCone K, (thetaSeries a F x - a 0 * F 0) * χ x *
        (mixedEmbedding.norm x : ℂ) ^ (s - 1) =
      (Units.torsionOrder K : ℂ) * ∑' p, a (gen p) * (χ (mixedEmbedding K (gen p : K)))⁻¹ *
        (mixedEmbedding.norm (mixedEmbedding K (gen p : K)) : ℂ) ^ (-s) *
          ∫ y, F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
  have hpos : ∀ x ∈ fundamentalCone K, mixedEmbedding.norm x ≠ 0 := fun x hx =>
    (fundamentalCone.norm_pos_of_mem hx).ne'
  -- the integrand as a sum over `Kˣ`
  have hpt : ∀ x ∈ fundamentalCone K, (thetaSeries a F x - a 0 * F 0) * χ x *
      (mixedEmbedding.norm x : ℂ) ^ (s - 1) = ∑' γ : Kˣ, unfoldIntegrand a F χ s γ x := by
    intro x hx
    have h0 := (hS x hx).tsum_eq_add_tsum_ite 0
    have hK : ∑' γ : K, (if γ = 0 then 0 else a γ * F (mixedEmbedding K γ * x)) =
        ∑' γ : Kˣ, a γ * F (mixedEmbedding K (γ : K) * x) := by
      have hsupp : Function.support (fun γ : K => if γ = 0 then 0 else
          a γ * F (mixedEmbedding K γ * x)) ⊆ Set.range (Units.val : Kˣ → K) := by
        intro γ hγ
        have hγ0 : γ ≠ 0 := fun h => hγ (by simp [h])
        exact ⟨Units.mk0 γ hγ0, rfl⟩
      rw [← (Function.Injective.tsum_eq (fun _ _ h => Units.ext h) hsupp)]
      exact tsum_congr fun γ => by simp [γ.ne_zero]
    rw [thetaSeries, h0, hK, map_zero, zero_mul, add_sub_cancel_left, ← tsum_mul_right,
      ← tsum_mul_right]
    rfl
  -- integrability and the integrals of the norms
  have hI : ∀ γ : Kˣ, Integrable (unfoldIntegrand a F χ s γ) :=
    integrable_unfoldIntegrand hχmul hχ1 hint
  -- the sums over the units
  have hfib : ∀ p, HasSum (fun u : (𝓞 K)ˣ =>
      ∫ x in fundamentalCone K, unfoldIntegrand a F χ s (e (p, u)) x)
        ((Units.torsionOrder K : ℝ) • ∫ y, unfoldIntegrand a F χ s (gen p) y) := by
    intro p
    convert hasSum_setIntegral_unit_smul (hI (gen p)) using 2 with u
    refine setIntegral_congr_fun (measurableSet_fundamentalCone K) fun x hx => ?_
    rw [he]
    exact unfoldIntegrand_units_mul hχmul hunit F s u (gen p) (hpos x hx)
  have hfibN : ∀ p, HasSum (fun u : (𝓞 K)ˣ =>
      ∫ x in fundamentalCone K, ‖unfoldIntegrand a F χ s (e (p, u)) x‖)
        ((Units.torsionOrder K : ℝ) • ∫ y, ‖unfoldIntegrand a F χ s (gen p) y‖) := by
    intro p
    convert hasSum_setIntegral_unit_smul (hI (gen p)).norm using 2 with u
    refine setIntegral_congr_fun (measurableSet_fundamentalCone K) fun x hx => ?_
    rw [he, unfoldIntegrand_units_mul hχmul hunit F s u (gen p) (hpos x hx)]
  -- summability of the integrals of the norms over `Kˣ`
  have hsumN : Summable fun γ : Kˣ =>
      ∫ x in fundamentalCone K, ‖unfoldIntegrand a F χ s γ x‖ := by
    rw [← e.summable_iff]
    refine (summable_prod_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _)).mpr
      ⟨fun p => (hfibN p).summable, ?_⟩
    refine ((hsum.mul_right (∫ y, ‖F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)‖)).mul_left
      (Units.torsionOrder K : ℝ)).congr fun p => ?_
    rw [(hfibN p).tsum_eq, smul_eq_mul, integral_norm_unfoldIntegrand hχmul hχ1]
  -- interchange of sum and integral, and summation over the orbits
  have hH := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (fundamentalCone K)) (fun γ => (hI γ).integrableOn) hsumN
  have hP := (e.hasSum_iff.mpr hH).prod_fiberwise hfib
  rw [setIntegral_congr_fun (measurableSet_fundamentalCone K) hpt, ← hP.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [integral_unfoldIntegrand hχmul hχ1, Complex.real_smul]
  push_cast
  ring

include hχmul hχ1 in
/-- `integral_thetaSeries_unfold_of_summable` for coefficients bounded and supported in a
fractional ideal and `F` with Gaussian decay. -/
theorem integral_thetaSeries_unfold {P : Type*} (gen : P → Kˣ) (e : P × (𝓞 K)ˣ ≃ Kˣ)
    (he : ∀ p u, ((e (p, u) : Kˣ) : K) = ((u : 𝓞 K) : K) * (gen p : K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K → ℂ}
    (ha : ∀ γ, a γ ≠ 0 → γ ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) {M : ℝ} (hM : ∀ γ, ‖a γ‖ ≤ M)
    (hunit : ∀ (u : (𝓞 K)ˣ) (γ : K),
      a (((u : 𝓞 K) : K) * γ) = χ (mixedEmbedding K ((u : 𝓞 K) : K)) * a γ)
    {F : mixedSpace K → ℂ} {C c : ℝ} (hc : 0 < c)
    (hF : ∀ z, ‖F z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) (s : ℂ)
    (hsum : Summable fun p => ‖a (gen p)‖ * ‖χ (mixedEmbedding K (gen p : K))‖⁻¹ *
      mixedEmbedding.norm (mixedEmbedding K (gen p : K)) ^ (-s.re))
    (hint : Integrable fun y => F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1)) :
    ∫ x in fundamentalCone K, (thetaSeries a F x - a 0 * F 0) * χ x *
        (mixedEmbedding.norm x : ℂ) ^ (s - 1) =
      (Units.torsionOrder K : ℂ) * ∑' p, a (gen p) * (χ (mixedEmbedding K (gen p : K)))⁻¹ *
        (mixedEmbedding.norm (mixedEmbedding K (gen p : K)) : ℂ) ^ (-s) *
          ∫ y, F y * χ y * (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
  refine integral_thetaSeries_unfold_of_summable hχmul hχ1 gen e he hunit (fun x hx => ?_) s
    hsum hint
  obtain ⟨m, hm, hmx⟩ := exists_pos_le_normAtPlace (fundamentalCone.norm_pos_of_mem hx).ne'
  obtain ⟨u, hu, hub, -⟩ := exists_thetaSeries_decay I ha hM hc hF hm
  exact Summable.of_norm_bounded hu (hub x hmx)

include hχmul hχ1 in
/-- **Unfolding the dual theta integral.** With `b` transforming under the units like `χ⁻¹`
(`b(u μ) = χ(u)⁻¹ b(μ)`), bounded and supported in a fractional ideal, and `G` with Gaussian
decay, if `∑_p |b(gen p⁻¹)| |χ(gen p)|⁻¹ N(gen p)^(Re s)` converges and `G(y⁻¹) χ(y) N(y)^(-s-1)`
is integrable, then
`∫_C (θ(b, G)(x⁻¹) - b(0) G(0)) χ(x) N(x)^(-s-1) dx
  = w ∑_p b(gen p⁻¹) χ(gen p)⁻¹ N(gen p)^s ∫_V G(y⁻¹) χ(y) N(y)^(-s-1) dy`. -/
theorem integral_thetaSeries_inv_unfold {P : Type*} (gen : P → Kˣ) (e : P × (𝓞 K)ˣ ≃ Kˣ)
    (he : ∀ p u, ((e (p, u) : Kˣ) : K) = ((u : 𝓞 K) : K) * (gen p : K))
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {b : K → ℂ}
    (hb : ∀ γ, b γ ≠ 0 → γ ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) {M : ℝ} (hM : ∀ γ, ‖b γ‖ ≤ M)
    (hbunit : ∀ (u : (𝓞 K)ˣ) (γ : K),
      b (((u : 𝓞 K) : K) * γ) = (χ (mixedEmbedding K ((u : 𝓞 K) : K)))⁻¹ * b γ)
    {G : mixedSpace K → ℂ} {C c : ℝ} (hc : 0 < c)
    (hG : ∀ z, ‖G z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) (s : ℂ)
    (hsum : Summable fun p => ‖b ((gen p)⁻¹ : Kˣ)‖ * ‖χ (mixedEmbedding K (gen p : K))‖⁻¹ *
      mixedEmbedding.norm (mixedEmbedding K (gen p : K)) ^ s.re)
    (hint : Integrable fun y => G y⁻¹ * χ y * (mixedEmbedding.norm y : ℂ) ^ (-s - 1)) :
    ∫ x in fundamentalCone K, (thetaSeries b G x⁻¹ - b 0 * G 0) * χ x *
        (mixedEmbedding.norm x : ℂ) ^ (-s - 1) =
      (Units.torsionOrder K : ℂ) * ∑' p, b ((gen p)⁻¹ : Kˣ) *
        (χ (mixedEmbedding K (gen p : K)))⁻¹ *
          (mixedEmbedding.norm (mixedEmbedding K (gen p : K)) : ℂ) ^ s *
            ∫ y, G y⁻¹ * χ y * (mixedEmbedding.norm y : ℂ) ^ (-s - 1) := by
  -- the inverted theta series
  have hinvθ : ∀ x : mixedSpace K,
      thetaSeries (fun γ => b γ⁻¹) (fun y => G y⁻¹) x = thetaSeries b G x⁻¹ := by
    intro x
    unfold thetaSeries
    calc ∑' γ : K, b γ⁻¹ * G (mixedEmbedding K γ * x)⁻¹ =
        ∑' γ : K, (fun μ => b μ * G (mixedEmbedding K μ * x⁻¹)) γ⁻¹ :=
          tsum_congr fun γ => by simp only [mul_inv, mixedEmbedding_inv]
      _ = _ := (Equiv.inv K).tsum_eq (fun μ => b μ * G (mixedEmbedding K μ * x⁻¹))
  -- unit behaviour of the inverted coefficients
  have hunit : ∀ (u : (𝓞 K)ˣ) (γ : K), b (((u : 𝓞 K) : K) * γ)⁻¹ =
      χ (mixedEmbedding K ((u : 𝓞 K) : K)) * b γ⁻¹ := by
    intro u γ
    have hu1 : ((u : 𝓞 K) : K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) u.mul_inv
    have hχu : χ (mixedEmbedding K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        (χ (mixedEmbedding K ((u : 𝓞 K) : K)))⁻¹ := by
      have h1 := hχmul (mixedEmbedding K ((u : 𝓞 K) : K))
        (mixedEmbedding K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) (norm_mixedEmbedding_unit_ne_zero u)
        (norm_mixedEmbedding_unit_ne_zero u⁻¹)
      rw [← map_mul, hu1, map_one, hχ1] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    rw [mul_inv, ← coe_units_inv, hbunit, hχu, inv_inv]
  -- pointwise summability
  have hS : ∀ x ∈ fundamentalCone K, Summable fun γ : K =>
      b γ⁻¹ * G (mixedEmbedding K γ * x)⁻¹ := by
    intro x hx
    have hx' : mixedEmbedding.norm x⁻¹ ≠ 0 := by
      rw [norm_inv']
      exact inv_ne_zero (fundamentalCone.norm_pos_of_mem hx).ne'
    obtain ⟨m, hm, hmx⟩ := exists_pos_le_normAtPlace hx'
    obtain ⟨u, hu, hub, -⟩ := exists_thetaSeries_decay J hb hM hc hG hm
    have h1 : Summable fun μ : K => b μ * G (mixedEmbedding K μ * x⁻¹) :=
      Summable.of_norm_bounded hu (hub x⁻¹ hmx)
    refine ((Equiv.inv K).summable_iff.mpr h1).congr fun γ => ?_
    simp only [Function.comp_apply, Equiv.inv_apply, mul_inv, mixedEmbedding_inv]
  have hsum' : Summable fun p => ‖b (gen p : K)⁻¹‖ * ‖χ (mixedEmbedding K (gen p : K))‖⁻¹ *
      mixedEmbedding.norm (mixedEmbedding K (gen p : K)) ^ (-(-s).re) := by
    refine hsum.congr fun p => ?_
    rw [Complex.neg_re, neg_neg, Units.val_inv_eq_inv_val]
  have h := integral_thetaSeries_unfold_of_summable hχmul hχ1 gen e he
    (a := fun γ => b γ⁻¹) hunit (F := fun y => G y⁻¹) hS (-s) hsum' hint
  have hcongr : ∫ x in fundamentalCone K, (thetaSeries b G x⁻¹ - b 0 * G 0) * χ x *
      (mixedEmbedding.norm x : ℂ) ^ (-s - 1) =
        ∫ x in fundamentalCone K, (thetaSeries (fun γ => b γ⁻¹) (fun y => G y⁻¹) x -
          b 0⁻¹ * G 0⁻¹) * χ x * (mixedEmbedding.norm x : ℂ) ^ (-s - 1) := by
    refine setIntegral_congr_fun (measurableSet_fundamentalCone K) fun x _ => ?_
    rw [hinvθ, inv_zero (G₀ := K), mixedSpace_inv_zero]
  rw [hcongr, h, neg_neg]
  congr 1
  refine tsum_congr fun p => ?_
  rw [Units.val_inv_eq_inv_val]

end Unfolding

end Langlands.Global.Hecke
