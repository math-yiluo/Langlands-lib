import Langlands.Correspondence.Laumon.Traits
import Langlands.CommutativeAlgebra.HenselianSimpleRoots

/-!
# The end ring is a henselian discrete valuation ring

The ring `endRing k` of power series separable algebraic over `k(t)` embeds into `k⟦t⟧` by
`endPowerSeriesHom k`. This module shows that an element of `endRing k` is a unit exactly when its
constant coefficient is nonzero, that divisibility in `endRing k` is divisibility of power series,
and deduces that `endRing k` is a discrete valuation ring with uniformizer `t` and a henselian
local ring.
-/

noncomputable section

universe u

open Polynomial IsLocalRing

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

/-- The power series of an element of the end ring is its Laurent series. -/
theorem ofPowerSeries_endPowerSeriesHom (x : endRing k) :
    HahnSeries.ofPowerSeries ℤ k (endPowerSeriesHom k x) = ((x : endField k) : LaurentSeries k) :=
  congrArg Subtype.val ((RingEquiv.ofBijective (HahnSeries.ofPowerSeries ℤ k).rangeRestrict
    ⟨fun _ _ h => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply ⟨_, x.2⟩)

theorem endPowerSeriesHom_eq_iff (x : endRing k) (p : PowerSeries k) :
    endPowerSeriesHom k x = p ↔
      HahnSeries.ofPowerSeries ℤ k p = ((x : endField k) : LaurentSeries k) := by
  rw [← ofPowerSeries_endPowerSeriesHom]
  exact ⟨fun h => by rw [h], fun h => (HahnSeries.ofPowerSeries_injective h).symm⟩

theorem endPowerSeriesHom_injective : Function.Injective (endPowerSeriesHom k) := by
  intro x y h
  have := congrArg (HahnSeries.ofPowerSeries ℤ k) h
  rw [ofPowerSeries_endPowerSeriesHom, ofPowerSeries_endPowerSeriesHom] at this
  exact Subtype.ext (Subtype.ext this)

/-- An element of the end field lies in the end ring when its Laurent series is a power series. -/
theorem mem_endRing_iff (z : endField k) :
    z ∈ endRing k ↔ ∃ p : PowerSeries k, HahnSeries.ofPowerSeries ℤ k p = (z : LaurentSeries k) :=
  Iff.rfl

theorem endPowerSeriesHom_endUniformizer (e : FourierEnd) :
    endPowerSeriesHom k (endUniformizer k e) = PowerSeries.X := by
  rw [endPowerSeriesHom_eq_iff]
  exact (algebraMap_ratFunc_X k).symm

theorem endPowerSeriesHom_endConstantHom (c : k) :
    endPowerSeriesHom k (endConstantHom k c) = PowerSeries.C c := by
  rw [endPowerSeriesHom_eq_iff]
  exact (algebraMap_ratFunc_algebraMap k c).symm

/-- On polynomials, the chart coordinate followed by the power series map is the inclusion
`k[X] → k⟦X⟧`. -/
theorem endPowerSeriesHom_comp_endChartCoordinate (e : FourierEnd) :
    (endPowerSeriesHom k).comp (endChartCoordinate k e) = Polynomial.coeToPowerSeries.ringHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp [endChartCoordinate, endPowerSeriesHom_endConstantHom]
  · simp [endChartCoordinate, endPowerSeriesHom_endUniformizer]

theorem endPowerSeriesHom_endChartCoordinate (e : FourierEnd) (p : k[X]) :
    endPowerSeriesHom k (endChartCoordinate k e p) = (p : PowerSeries k) :=
  RingHom.congr_fun (endPowerSeriesHom_comp_endChartCoordinate k e) p

theorem endResidue_apply (x : endRing k) :
    endResidue k x = PowerSeries.constantCoeff (endPowerSeriesHom k x) := rfl

/-- **Units of the end ring.** An element of `endRing k` is a unit if and only if its constant
coefficient is nonzero. -/
theorem isUnit_endRing_iff (x : endRing k) :
    IsUnit x ↔ PowerSeries.constantCoeff (endPowerSeriesHom k x) ≠ 0 := by
  constructor
  · intro h
    have := h.map (endPowerSeriesHom k)
    rw [PowerSeries.isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  · intro h
    have hx0 : (x : endField k) ≠ 0 := by
      intro h0
      apply h
      have : x = 0 := Subtype.ext h0
      rw [this, map_zero, map_zero]
    have hΛ0 : ((x : endField k) : LaurentSeries k) ≠ 0 := by
      exact_mod_cast hx0
    have hmem : (x : endField k)⁻¹ ∈ endRing k := by
      refine ⟨(endPowerSeriesHom k x)⁻¹, ?_⟩
      change HahnSeries.ofPowerSeries ℤ k (endPowerSeriesHom k x)⁻¹ =
        (((x : endField k)⁻¹ : endField k) : LaurentSeries k)
      rw [IntermediateField.coe_inv]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← ofPowerSeries_endPowerSeriesHom, ← map_mul, PowerSeries.inv_mul_cancel _ h, map_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

/-- **Divisibility in the end ring** is divisibility of power series. -/
theorem endRing_dvd_iff (x y : endRing k) :
    x ∣ y ↔ endPowerSeriesHom k x ∣ endPowerSeriesHom k y := by
  refine ⟨map_dvd _, ?_⟩
  rintro ⟨q, hq⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, zero_mul] at hq
    have : y = 0 := endPowerSeriesHom_injective k (by rw [hq, map_zero])
    rw [this]
    exact dvd_zero x
  · have hx0 : (x : endField k) ≠ 0 := fun h => hx (Subtype.ext h)
    have hΛ0 : ((x : endField k) : LaurentSeries k) ≠ 0 := by exact_mod_cast hx0
    have hmem : (y : endField k) * (x : endField k)⁻¹ ∈ endRing k := by
      refine ⟨q, ?_⟩
      change HahnSeries.ofPowerSeries ℤ k q =
        (((y : endField k) * (x : endField k)⁻¹ : endField k) : LaurentSeries k)
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, eq_mul_inv_iff_mul_eq₀ hΛ0,
        ← ofPowerSeries_endPowerSeriesHom, ← ofPowerSeries_endPowerSeriesHom, ← map_mul, hq,
        mul_comm]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    change (y : endField k) = (x : endField k) * ((y : endField k) * (x : endField k)⁻¹)
    rw [mul_comm (y : endField k), ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

/-- **Factorization in the end ring.** Every nonzero element of `endRing k` is `t ^ n` times a
unit. -/
theorem exists_eq_endUniformizer_pow_mul (e : FourierEnd) (x : endRing k) (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : endRing k), IsUnit v ∧ x = endUniformizer k e ^ n * v := by
  set p := endPowerSeriesHom k x with hp
  have hp0 : p ≠ 0 := fun h => hx (endPowerSeriesHom_injective k (by rw [← hp, h, map_zero]))
  have hdvd : endUniformizer k e ^ p.order.toNat ∣ x := by
    rw [endRing_dvd_iff, map_pow, endPowerSeriesHom_endUniformizer]
    exact ⟨_, PowerSeries.X_pow_order_mul_divXPowOrder.symm⟩
  obtain ⟨v, hv⟩ := hdvd
  refine ⟨p.order.toNat, v, ?_, hv⟩
  have hser : endPowerSeriesHom k v = p.divXPowOrder := by
    have h1 := congrArg (endPowerSeriesHom k) hv
    rw [map_mul, map_pow, endPowerSeriesHom_endUniformizer, ← hp] at h1
    have h2 := (PowerSeries.X_pow_order_mul_divXPowOrder (f := p))
    exact mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) (h1.symm.trans h2.symm)
  rw [isUnit_endRing_iff, hser, PowerSeries.constantCoeff_divXPowOrder]
  exact PowerSeries.coeff_order hp0

/-- The uniformizer `t` is irreducible in the end ring. -/
theorem irreducible_endUniformizer (e : FourierEnd) : Irreducible (endUniformizer k e) := by
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · rw [isUnit_endRing_iff, endPowerSeriesHom_endUniformizer] at h
    simp at h
  · have h := congrArg (endPowerSeriesHom k) hab
    rw [map_mul, endPowerSeriesHom_endUniformizer] at h
    rw [isUnit_endRing_iff, isUnit_endRing_iff]
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    obtain ⟨ha, hb⟩ := hc
    rw [← PowerSeries.X_dvd_iff] at ha hb
    have h2 := mul_dvd_mul ha hb
    rw [← h, ← pow_two] at h2
    rw [PowerSeries.X_pow_dvd_iff] at h2
    simpa using h2 1 (by norm_num)

/-- **The end ring is a discrete valuation ring.** -/
instance isDiscreteValuationRing_endRing : IsDiscreteValuationRing (endRing k) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨endUniformizer k .zero, irreducible_endUniformizer k .zero, fun {x} hx => by
      obtain ⟨n, v, hv, rfl⟩ := exists_eq_endUniformizer_pow_mul k .zero x hx
      exact ⟨n, hv.unit, rfl⟩⟩

theorem mem_maximalIdeal_endRing_iff (x : endRing k) :
    x ∈ maximalIdeal (endRing k) ↔ PowerSeries.constantCoeff (endPowerSeriesHom k x) = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_endRing_iff, not_not]

theorem mem_maximalIdeal_powerSeries_iff (p : PowerSeries k) :
    p ∈ maximalIdeal (PowerSeries k) ↔ PowerSeries.constantCoeff p = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

/-- The composite `endRing k → endField k → k((t))` is the power series map followed by the
inclusion of power series. -/
theorem algebraMap_comp_subtype_endRing :
    (algebraMap (endField k) (LaurentSeries k)).comp (endRing k).subtype =
      (HahnSeries.ofPowerSeries ℤ k).comp (endPowerSeriesHom k) := by
  exact RingHom.ext fun x => (ofPowerSeries_endPowerSeriesHom k x).symm

theorem aeval_map_subtype_endRing (f : (endRing k)[X]) (β : PowerSeries k) :
    aeval (HahnSeries.ofPowerSeries ℤ k β) (f.map (endRing k).subtype) =
      HahnSeries.ofPowerSeries ℤ k ((f.map (endPowerSeriesHom k)).eval β) := by
  rw [aeval_def, eval₂_map, algebraMap_comp_subtype_endRing, eval_map, hom_eval₂]

/-- **The end ring is a henselian local ring.** A simple residual root of a monic polynomial over
`endRing k` lifts to a root `α ∈ k⟦t⟧`, since `k⟦t⟧` is henselian; `α` is a simple root, hence
separable over `endField k`, hence over `k(t)`, so it lies in `endField k`. -/
instance henselianLocalRing_endRing : HenselianLocalRing (endRing k) where
  is_henselian f hf a₀ h₁ h₂ := by
    classical
    have h₁' : (f.map (endPowerSeriesHom k)).eval (endPowerSeriesHom k a₀) ∈
        maximalIdeal (PowerSeries k) := by
      rw [eval_map_apply, mem_maximalIdeal_powerSeries_iff]
      exact (mem_maximalIdeal_endRing_iff k _).1 h₁
    have h₂' : IsUnit ((f.map (endPowerSeriesHom k)).derivative.eval (endPowerSeriesHom k a₀)) := by
      rw [derivative_map, eval_map_apply]
      exact h₂.map _
    obtain ⟨α, hα, hα'⟩ := HenselianLocalRing.is_henselian (f.map (endPowerSeriesHom k))
      (hf.map _) _ h₁' h₂'
    obtain ⟨αΛ, hαΛ⟩ : ∃ z, z = HahnSeries.ofPowerSeries ℤ k α := ⟨_, rfl⟩
    obtain ⟨fF, hfF⟩ : ∃ g : (endField k)[X], g = f.map (endRing k).subtype := ⟨_, rfl⟩
    have hroot : aeval αΛ fF = 0 := by
      rw [hαΛ, hfF, aeval_map_subtype_endRing, hα.eq_zero, map_zero]
    -- the derivative at `α` is a unit of `k⟦t⟧`
    have hunit : IsUnit ((f.map (endPowerSeriesHom k)).derivative.eval α) := by
      obtain ⟨c, hc⟩ := sub_dvd_eval_sub α (endPowerSeriesHom k a₀)
        (f.map (endPowerSeriesHom k)).derivative
      have hm : (f.map (endPowerSeriesHom k)).derivative.eval α -
          (f.map (endPowerSeriesHom k)).derivative.eval (endPowerSeriesHom k a₀) ∈
            maximalIdeal (PowerSeries k) := by
        rw [hc]
        exact Ideal.mul_mem_right _ _ hα'
      have hres := (residue_eq_zero_iff _).2 hm
      rw [map_sub, sub_eq_zero] at hres
      rw [← residue_ne_zero_iff_isUnit] at h₂' ⊢
      rwa [hres]
    have hder : aeval αΛ (derivative fF) ≠ 0 := by
      rw [hfF, derivative_map, hαΛ, aeval_map_subtype_endRing, ← derivative_map]
      intro h0
      exact hunit.ne_zero (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
    have hint : IsIntegral (endField k) αΛ := ⟨fF, hfF ▸ hf.map _, hroot⟩
    have hsep : IsSeparable (endField k) αΛ := by
      change (minpoly (endField k) αΛ).Separable
      rw [separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
      intro h0
      obtain ⟨g, hg⟩ := minpoly.dvd (endField k) αΛ hroot
      apply hder
      rw [hg, derivative_mul, h0, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]
    have hmem : αΛ ∈ separableClosure (endField k) (LaurentSeries k) :=
      mem_separableClosure_iff.2 hsep
    rw [show separableClosure (endField k) (LaurentSeries k) = ⊥ from
      separableClosure.separableClosure_eq_bot (RatFunc k) (LaurentSeries k)] at hmem
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hmem
    have hyΛ : HahnSeries.ofPowerSeries ℤ k α = (y : LaurentSeries k) := by
      rw [← hαΛ, ← hy]
      rfl
    have hyR : y ∈ endRing k := ⟨α, hyΛ⟩
    have hya : endPowerSeriesHom k ⟨y, hyR⟩ = α := (endPowerSeriesHom_eq_iff k _ _).2 hyΛ
    refine ⟨⟨y, hyR⟩, ?_, ?_⟩
    · show f.eval _ = 0
      apply endPowerSeriesHom_injective k
      rw [map_zero, ← eval_map_apply, hya]
      exact hα.eq_zero
    · rw [mem_maximalIdeal_endRing_iff, (endPowerSeriesHom k).map_sub, hya]
      exact (mem_maximalIdeal_powerSeries_iff k _).1 hα'

end Langlands.Henniart.Laumon
