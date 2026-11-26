import Langlands.Shimura.PEL.HarrisNormalizedPolarization
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # The primitive pairing of the fixed Harris source lattice -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "pairing" => D.harrisHodgePELIntegralPairing C
local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C

private def pairingValueIdeal {M : Type*} [AddCommGroup M] (b : LinearMap.BilinForm ℤ M) :
    Ideal ℤ :=
  Ideal.span (Set.range (fun p : M × M => b p.1 p.2))

private theorem pairing_mem_valueIdeal {M : Type*} [AddCommGroup M]
    (b : LinearMap.BilinForm ℤ M) (x y : M) : b x y ∈ pairingValueIdeal b :=
  Ideal.subset_span ⟨(x, y), rfl⟩

/-- An integer generator of the ideal of values of the original integral pairing. -/
def harrisHodgePELPairingContent : ℤ :=
  Submodule.IsPrincipal.generator (pairingValueIdeal pairing)

local notation "content" => D.harrisHodgePELPairingContent C

theorem harrisHodgePELPairingContent_ne_zero : content ≠ 0 := by
  have : Nontrivial L := Module.nontrivial_of_finrank_pos
    (PEL.HarrisPolarizedWeilLevel.harrisIntegralLattice_finrank_pos D C)
  intro hc
  have hb : pairingValueIdeal pairing = ⊥ := by
    rw [← Ideal.span_singleton_generator (pairingValueIdeal pairing)]
    change Ideal.span {content} = ⊥
    rw [hc, Ideal.span_singleton_eq_bot]
  apply (D.harrisHodgePELIntegralPairing_nondegenerate C).ne_zero
  ext x y
  have h := pairing_mem_valueIdeal pairing x y
  rwa [hb, Ideal.mem_bot] at h

private def multiplyContent : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.toSpanSingleton ℤ ℤ content

private theorem multiplyContent_injective : Function.Injective (multiplyContent D C) :=
  fun _ _ h => mul_right_cancel₀ (D.harrisHodgePELPairingContent_ne_zero C) h

private theorem pairing_mem_range_multiplyContent (x y : L) :
    pairing x y ∈ LinearMap.range (multiplyContent D C) := by
  obtain ⟨a, ha⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd
    (pairingValueIdeal pairing)).mp (pairing_mem_valueIdeal pairing x y)
  exact ⟨a, (mul_comm a content).trans ha.symm⟩

/-- Divide the original integral pairing by a generator of its value ideal. -/
def harrisHodgePELPrimitivePairing : LinearMap.BilinForm ℤ L :=
  LinearMap.restrictScalarsRange₂ LinearMap.id LinearMap.id (multiplyContent D C)
    (multiplyContent_injective D C) pairing (pairing_mem_range_multiplyContent D C)

local notation "primitive" => D.harrisHodgePELPrimitivePairing C

theorem harrisHodgePELPrimitivePairing_mul (x y : L) :
    content * primitive x y = pairing x y := by
  rw [mul_comm]
  exact LinearMap.restrictScalarsRange₂_apply LinearMap.id LinearMap.id
    (multiplyContent D C) (multiplyContent_injective D C) pairing
    (pairing_mem_range_multiplyContent D C) x y

theorem harrisHodgePELPrimitivePairing_isAlt : (primitive).IsAlt := by
  intro x
  apply mul_left_cancel₀ (D.harrisHodgePELPairingContent_ne_zero C)
  rw [D.harrisHodgePELPrimitivePairing_mul C, mul_zero]
  exact D.harrisHodgePELIntegralPairing_isAlt C x

theorem harrisHodgePELPrimitivePairing_nondegenerate : (primitive).Nondegenerate := by
  have hb := D.harrisHodgePELIntegralPairing_nondegenerate C
  constructor
  · intro x hx
    apply hb.1 x
    intro y
    rw [← D.harrisHodgePELPrimitivePairing_mul C x y, hx y, mul_zero]
  · intro y hy
    apply hb.2 y
    intro x
    rw [← D.harrisHodgePELPrimitivePairing_mul C x y, hy x, mul_zero]

/-- The primitive pairing values span the unit ideal of the integers. -/
theorem harrisHodgePELPrimitivePairing_span :
    Ideal.span (Set.range (fun p : L × L => primitive p.1 p.2)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  let m := multiplyContent D C
  have hle : (pairingValueIdeal pairing : Submodule ℤ ℤ) ≤
      Submodule.map m (pairingValueIdeal primitive) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    apply Submodule.mem_map.mpr
    exact ⟨primitive x y, pairing_mem_valueIdeal primitive x y,
      (mul_comm _ _).trans (D.harrisHodgePELPrimitivePairing_mul C x y)⟩
  have hc : content ∈ pairingValueIdeal pairing :=
    Submodule.IsPrincipal.generator_mem (pairingValueIdeal pairing)
  obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp (hle hc)
  have ha1 : a = 1 := multiplyContent_injective D C (he.trans (one_mul content).symm)
  exact ha1 ▸ ha

/-- The actual adelic form scaled by the inverse of the integer content. -/
def harrisHodgePELPrimitiveAdelicForm : LinearMap.BilinForm Af Vf :=
  (algebraMap ℚ Af (content : ℚ)⁻¹) • (D.harrisHodgePELForm C).baseChange Af

local notation "primitiveAdele" => D.harrisHodgePELPrimitiveAdelicForm C

/-- Rescaling by the content recovers the unchanged rational adelic form. -/
theorem harrisHodgePELPrimitiveAdelicForm_mul (v w : Vf) :
    algebraMap ℚ Af (content : ℚ) * primitiveAdele v w =
      (D.harrisHodgePELForm C).baseChange Af v w := by
  have hc : (content : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (D.harrisHodgePELPairingContent_ne_zero C)
  unfold harrisHodgePELPrimitiveAdelicForm
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hc, map_one, one_mul]

/-- The integral primitive form is the restriction on the original pure generators. -/
theorem harrisHodgePELPrimitiveAdelicForm_tmul (x y : L) :
    primitiveAdele ((1 : Af) ⊗ₜ[ℚ] (x : A)) ((1 : Af) ⊗ₜ[ℚ] (y : A)) =
      (primitive x y : Af) := by
  rw [harrisHodgePELPrimitiveAdelicForm, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.baseChange_tmul, one_mul, ← Algebra.algebraMap_eq_smul_one,
    ← harrisHodgePELIntegralPairing_cast]
  have hc : (content : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (D.harrisHodgePELPairingContent_ne_zero C)
  rw [← D.harrisHodgePELPrimitivePairing_mul C x y, Int.cast_mul, ← map_intCast (algebraMap ℚ Af)
    (primitive x y)]
  change algebraMap ℚ Af (content : ℚ)⁻¹ *
    algebraMap ℚ Af ((content : ℚ) * (primitive x y : ℚ)) =
      algebraMap ℚ Af (primitive x y : ℚ)
  rw [← map_mul, inv_mul_cancel_left₀ hc]

local instance integralScalarAction : Module Rf Vf := Module.compHom _ (Rf).subtype

/-- The rescaled adelic form is integral on the full fixed source lattice. -/
theorem harrisHodgePELPrimitiveAdelicForm_mem {v w : Vf} (hv : v ∈ Λf) (hw : w ∈ Λf) :
    primitiveAdele v w ∈ Rf := by
  let gens := Set.range (fun x : L => (1 : Af) ⊗ₜ[ℚ] (x : A))
  change v ∈ Submodule.span Rf gens at hv
  change w ∈ Submodule.span Rf gens at hw
  induction hv, hw using Submodule.span_induction₂ with
  | mem_mem v w hv hw =>
    obtain ⟨x, rfl⟩ := hv
    obtain ⟨y, rfl⟩ := hw
    rw [harrisHodgePELPrimitiveAdelicForm_tmul]
    exact intCast_mem Rf _
  | zero_left w hw => simpa only [LinearMap.map_zero₂] using (Rf).zero_mem
  | zero_right v hv => simpa only [map_zero] using (Rf).zero_mem
  | add_left x y z _ _ _ hx hy =>
    rw [LinearMap.map_add₂]
    exact (Rf).add_mem hx hy
  | add_right x y z _ _ _ hy hz =>
    rw [map_add]
    exact (Rf).add_mem hy hz
  | smul_left r v w _ _ h =>
    change primitiveAdele ((r : Af) • v) w ∈ Rf
    rw [LinearMap.map_smul₂, smul_eq_mul]
    exact (Rf).mul_mem r.property h
  | smul_right r v w _ _ h =>
    change primitiveAdele v ((r : Af) • w) ∈ Rf
    rw [map_smul, smul_eq_mul]
    exact (Rf).mul_mem r.property h

end Langlands.Shimura.CentralSimpleUnitaryData
