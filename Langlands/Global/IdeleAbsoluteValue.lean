import Langlands.Global.Adelic
import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# The actual normalized idelic absolute value

Products use Mathlib's normalized finite-place norms and the archimedean
multiplicities. See the paired Markdown for the construction and scope.
-/

noncomputable section

universe uF

namespace Langlands.Global.IdeleAbsoluteValue

open Langlands.Global
open scoped Topology NNReal WithZero

variable (F : Type uF) [Field F] [NumberField F]

/-- The finite product of the normalized local norms, valued in nonnegative reals. -/
def finiteValue : FiniteIdeles F →* ℝ≥0 where
  toFun x := ⟨∏ᶠ v, ‖x.val v‖, finprod_nonneg fun _ => norm_nonneg _⟩
  map_one' := by
    apply NNReal.eq
    change (∏ᶠ v : FinitePlace F, ‖(1 : FiniteCompletion F v)‖) = 1
    simp
  map_mul' x y := by
    apply NNReal.eq
    change (∏ᶠ v, ‖x.val v * y.val v‖) =
      (∏ᶠ v, ‖x.val v‖) * ∏ᶠ v, ‖y.val v‖
    simp_rw [norm_mul]
    exact finprod_mul_distrib
      (NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm x)
      (NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm y)

@[simp]
theorem coe_finiteValue (x : FiniteIdeles F) :
    (finiteValue F x : ℝ) = ∏ᶠ v, ‖x.val v‖ := rfl

theorem finiteValue_eq_norm (x : FiniteIdeles F) :
    (finiteValue F x : ℝ) = ‖x.val‖ :=
  (NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit x).symm

/-- The open subgroup whose value and inverse are integral at every finite place. -/
def allIntegral : OpenSubgroup (FiniteIdeles F) where
  carrier := {x | (∀ v, x.val v ∈ v.adicCompletionIntegers F) ∧
    ∀ v, (x⁻¹).val v ∈ v.adicCompletionIntegers F}
  one_mem' := ⟨fun v => (v.adicCompletionIntegers F).one_mem,
    fun v => (v.adicCompletionIntegers F).one_mem⟩
  mul_mem' hx hy := by
    constructor
    · exact fun v => (v.adicCompletionIntegers F).mul_mem _ _ (hx.1 v) (hy.1 v)
    · simpa only [mul_inv_rev, Units.val_mul, RestrictedProduct.mul_apply] using
        fun v => (v.adicCompletionIntegers F).mul_mem _ _ (hy.2 v) (hx.2 v)
  inv_mem' hx := ⟨hx.2, by simpa using hx.1⟩
  isOpen' := by
    have h : IsOpen {x : FiniteAdeles F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_mem fun v =>
        Valued.isOpen_valuationSubring (FiniteCompletion F v)
    exact (h.preimage Units.continuous_val).inter
      (h.preimage (Units.continuous_val.comp continuous_inv))

set_option maxHeartbeats 800000 in
theorem norm_eq_one_of_mem_allIntegral (x : FiniteIdeles F)
    (hx : x ∈ allIntegral F) (v : FinitePlace F) : ‖x.val v‖ = 1 := by
  let u : (FiniteCompletion F v)ˣ :=
    { val := x.val v
      inv := (x⁻¹).val v
      val_inv := congrArg (fun z : FiniteAdeles F => z v) x.val_inv
      inv_val := congrArg (fun z : FiniteAdeles F => z v) x.inv_val }
  have hu : u ∈ (v.adicCompletionIntegers F).units := ⟨hx.1 v, hx.2 v⟩
  have hv : (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) (x.val v) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v) (a := u)).mp hu
  exact (Valued.toNormedField.norm_eq_one_iff
    (Γ₀ := ℤᵐ⁰) (x := x.val v)).mpr hv

theorem finiteValue_eq_one_of_mem_allIntegral (x : FiniteIdeles F)
    (hx : x ∈ allIntegral F) : finiteValue F x = 1 := by
  apply NNReal.eq
  change (∏ᶠ v, ‖x.val v‖) = 1
  simp only [norm_eq_one_of_mem_allIntegral F x hx, finprod_one]

private theorem continuous_finiteHom :
    Continuous (finiteValue F).toHomUnits := by
  apply continuous_of_continuousAt_one
  have he : (finiteValue F).toHomUnits =ᶠ[𝓝 (1 : FiniteIdeles F)] fun _ => 1 := by
    filter_upwards [(allIntegral F).isOpen.mem_nhds (allIntegral F).one_mem] with x hx
    apply Units.ext
    exact finiteValue_eq_one_of_mem_allIntegral F x hx
  exact continuousAt_const.congr_of_eventuallyEq he

/-- The genuine continuous finite idelic absolute value. -/
def finite : FiniteIdeles F →ₜ* ℝ≥0ˣ where
  toMonoidHom := (finiteValue F).toHomUnits
  continuous_toFun := continuous_finiteHom F

@[simp]
theorem coe_finite (x : FiniteIdeles F) :
    ((finite F x : ℝ≥0) : ℝ) = ∏ᶠ v, ‖x.val v‖ := rfl

/-- The archimedean norm product with multiplicity one at real and two at complex places. -/
def infiniteValue : (InfiniteAdeles F)ˣ →* ℝ≥0 where
  toFun x := ⟨∏ v, ‖x.val v‖ ^ v.mult,
    Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _⟩
  map_one' := by
    apply NNReal.eq
    change (∏ v : InfinitePlace F, ‖(1 : InfiniteCompletion F v)‖ ^ v.mult) = 1
    simp
  map_mul' x y := by
    apply NNReal.eq
    change (∏ v, ‖x.val v * y.val v‖ ^ v.mult) =
      (∏ v, ‖x.val v‖ ^ v.mult) * ∏ v, ‖y.val v‖ ^ v.mult
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]

@[simp]
theorem coe_infiniteValue (x : (InfiniteAdeles F)ˣ) :
    (infiniteValue F x : ℝ) = ∏ v, ‖x.val v‖ ^ v.mult := rfl

theorem infiniteValue_eq_norm (x : (InfiniteAdeles F)ˣ) :
    (infiniteValue F x : ℝ) = ‖x.val‖ := rfl

private theorem continuous_infiniteValue : Continuous (infiniteValue F) := by
  apply Continuous.subtype_mk
  have hval : Continuous (fun x : (InfiniteAdeles F)ˣ => x.val) := Units.continuous_val
  exact continuous_finsetProd _ fun v _ =>
    (((continuous_apply v).comp hval).norm).pow _

/-- The genuine continuous archimedean idelic absolute value. -/
def infinite : (InfiniteAdeles F)ˣ →ₜ* ℝ≥0ˣ where
  toMonoidHom := (infiniteValue F).toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_infiniteValue F, (continuous_infiniteValue F).comp continuous_inv⟩

@[simp]
theorem coe_infinite (x : (InfiniteAdeles F)ˣ) :
    ((infinite F x : ℝ≥0) : ℝ) = ∏ v, ‖x.val v‖ ^ v.mult := rfl

/-- The normalized absolute value on the actual full idele group. -/
def full : Ideles F →ₜ* ℝ≥0ˣ where
  toFun x := infinite F ((ideleProductEquiv F x).1) * finite F ((ideleProductEquiv F x).2)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun :=
    ((infinite F).continuous.comp (continuous_fst.comp (ideleProductEquiv F).continuous)).mul
      ((finite F).continuous.comp (continuous_snd.comp (ideleProductEquiv F).continuous))

@[simp]
theorem coe_full (x : Ideles F) :
    ((full F x : ℝ≥0) : ℝ) =
      (∏ v, ‖x.val.1 v‖ ^ v.mult) * ∏ᶠ v, ‖x.val.2 v‖ := rfl

theorem full_eq_norms (x : Ideles F) :
    ((full F x : ℝ≥0) : ℝ) = ‖x.val.1‖ * ‖x.val.2‖ := by
  change (infiniteValue F (ideleProductEquiv F x).1 : ℝ) *
    (finiteValue F (ideleProductEquiv F x).2 : ℝ) = _
  rw [infiniteValue_eq_norm, finiteValue_eq_norm]
  rfl

theorem full_pos (x : Ideles F) : 0 < ((full F x : ℝ≥0) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (full F x).ne_zero)

/-- The actual normalized product formula makes every principal idele have value one. -/
@[simp]
theorem full_diagonalUnits (a : Fˣ) : full F (diagonalUnits F a) = 1 := by
  apply Units.ext
  apply NNReal.eq
  rw [full_eq_norms]
  change ‖algebraMap F (InfiniteAdeles F) a.val‖ *
    ‖algebraMap F (FiniteAdeles F) a.val‖ = 1
  rw [NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm,
    NumberField.FiniteAdeleRing.coe_norm_eq_inv_abs_norm a.ne_zero]
  have hn : Algebra.norm ℚ a.val ≠ 0 := Algebra.norm_ne_zero_iff.mpr a.ne_zero
  exact_mod_cast (mul_inv_cancel₀ (abs_ne_zero.mpr hn))

/-- Descend the constructed norm character through the actual principal subgroup. -/
def ideleClass : IdeleClasses F →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift (principalIdeles F) (full F).toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact full_diagonalUnits F a)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff.mpr (full F).continuous

@[simp]
theorem ideleClass_class (x : Ideles F) :
    ideleClass F (ideleClassMap F x) = full F x := rfl

/-- The continuous descent is uniquely determined by its values on representatives. -/
theorem ideleClass_unique (χ : IdeleClasses F →ₜ* ℝ≥0ˣ)
    (hχ : ∀ x, χ (ideleClassMap F x) = full F x) : χ = ideleClass F := by
  apply ContinuousMonoidHom.ext
  intro c
  refine Quotient.inductionOn c (fun x => ?_)
  exact hχ x

@[simp]
theorem full_infiniteIdelesInclusion (x : (InfiniteAdeles F)ˣ) :
    full F (infiniteIdelesInclusion F x) = infinite F x := by
  change infinite F x * finite F 1 = _
  simp

@[simp]
theorem full_finiteIdelesInclusion (x : FiniteIdeles F) :
    full F (finiteIdelesInclusion F x) = finite F x := by
  change infinite F 1 * finite F x = _
  simp

/-- At a single finite place, the global character is the actual normalized local norm. -/
@[simp]
theorem coe_full_finiteIdeleInclusion (v : FinitePlace F)
    (x : (FiniteCompletion F v)ˣ) :
    ((full F (finiteIdeleInclusion F v x) : ℝ≥0) : ℝ) = ‖x.val‖ := by
  classical
  rw [coe_full]
  change (∏ w : InfinitePlace F, ‖(1 : InfiniteCompletion F w)‖ ^ w.mult) *
    (∏ᶠ w : FinitePlace F, ‖Pi.mulSingle v x.val w‖) = ‖x.val‖
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v (fun w hw => by
    simp [Pi.mulSingle_eq_of_ne hw])]
  simp

/-- At a single infinite place, the exponent retains its real/complex multiplicity. -/
@[simp]
theorem coe_full_infiniteIdeleInclusion (v : InfinitePlace F)
    (x : (InfiniteCompletion F v)ˣ) :
    ((full F (infiniteIdeleInclusion F v x) : ℝ≥0) : ℝ) = ‖x.val‖ ^ v.mult := by
  classical
  rw [coe_full]
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v x.val w‖ ^ w.mult) *
    (∏ᶠ w : FinitePlace F, ‖(1 : FiniteCompletion F w)‖) = ‖x.val‖ ^ v.mult
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single v (fun w _ hw => by
    simp [Pi.mulSingle_eq_of_ne hw]) (by simp)]
  simp

@[simp]
theorem coe_ideleClass_finiteClassInclusion (v : FinitePlace F)
    (x : (FiniteCompletion F v)ˣ) :
    ((ideleClass F (finiteClassInclusion F v x) : ℝ≥0) : ℝ) = ‖x.val‖ :=
  coe_full_finiteIdeleInclusion F v x

@[simp]
theorem coe_ideleClass_infiniteClassInclusion (v : InfinitePlace F)
    (x : (InfiniteCompletion F v)ˣ) :
    ((ideleClass F (infiniteClassInclusion F v x) : ℝ≥0) : ℝ) =
      ‖x.val‖ ^ v.mult :=
  coe_full_infiniteIdeleInclusion F v x

end Langlands.Global.IdeleAbsoluteValue
