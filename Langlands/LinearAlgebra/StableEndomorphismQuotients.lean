import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Adjacent kernel and range quotients of an endomorphism

The actual quotient modules `E_k = N_(k+1) / N_k` and `F_k = I_k / I_(k+1)`, where
`N_k = ker (t ^ k)` and `I_k = range (t ^ k)`, and the three linear maps
`E_(k+1) → E_k`, `E_k → F_k` and `F_k → F_(k+1)` induced by `t`, `t ^ k` and `t`,
from Renard 2026, Appendix C.II, proof of Lemma (iv), printed page 278 / PDF page 284.

The coefficient ring is an arbitrary ring `R`; Renard's complex vector spaces are the
case `R := ℂ`. No finiteness or stability hypothesis is made, and `k = 0` is allowed.
Kernel and image identifications and exactness are not part of this module.
-/

set_option autoImplicit false

namespace Langlands.LinearAlgebra.StableEndomorphism

universe uR uV

variable {R : Type uR} {V : Type uV} [Ring R] [AddCommGroup V] [Module R V]
variable (t : Module.End R V)

section Chains

/-- Renard's `N_k = ker (t ^ k)`, as an actual submodule of `V`. -/
abbrev kerPow (k : ℕ) : Submodule R V :=
  LinearMap.ker (t ^ k)

/-- Renard's `I_k = Im (t ^ k)`, as an actual submodule of `V`. -/
abbrev rangePow (k : ℕ) : Submodule R V :=
  LinearMap.range (t ^ k)

variable {t}

theorem mem_kerPow {k : ℕ} {x : V} : x ∈ kerPow t k ↔ (t ^ k) x = 0 :=
  LinearMap.mem_ker

theorem mem_rangePow {k : ℕ} {x : V} : x ∈ rangePow t k ↔ ∃ y, (t ^ k) y = x :=
  LinearMap.mem_range

variable (t)

/-- At `k = 0`, `N_0 = ker id = 0`. -/
theorem kerPow_zero : kerPow t 0 = ⊥ := by
  rw [kerPow, pow_zero, Module.End.one_eq_id, LinearMap.ker_id]

/-- At `k = 0`, `I_0 = Im id = V`. -/
theorem rangePow_zero : rangePow t 0 = ⊤ := by
  rw [rangePow, pow_zero, Module.End.one_eq_id, LinearMap.range_id]

variable {t}

/-- `t` maps `N_(k+1)` into `N_k`. -/
theorem apply_mem_kerPow {k : ℕ} {x : V} (hx : x ∈ kerPow t (k + 1)) : t x ∈ kerPow t k := by
  rw [mem_kerPow] at hx ⊢
  rwa [pow_succ, Module.End.mul_apply] at hx

/-- `t` maps `I_k` into `I_(k+1)`. -/
theorem apply_mem_rangePow {k : ℕ} {x : V} (hx : x ∈ rangePow t k) :
    t x ∈ rangePow t (k + 1) := by
  obtain ⟨y, rfl⟩ := mem_rangePow.mp hx
  exact mem_rangePow.mpr ⟨y, by rw [pow_succ', Module.End.mul_apply]⟩

/-- `t ^ k` maps all of `V` into `I_k`. -/
theorem pow_apply_mem_rangePow (k : ℕ) (x : V) : (t ^ k) x ∈ rangePow t k :=
  LinearMap.mem_range_self _ x

variable (t)

/-- The kernel chain increases: `N_k ≤ N_(k+1)`. -/
theorem kerPow_le_succ (k : ℕ) : kerPow t k ≤ kerPow t (k + 1) := by
  intro x hx
  rw [mem_kerPow] at hx ⊢
  rw [pow_succ', Module.End.mul_apply, hx, map_zero]

/-- The range chain decreases: `I_(k+1) ≤ I_k`. -/
theorem rangePow_succ_le (k : ℕ) : rangePow t (k + 1) ≤ rangePow t k := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_rangePow.mp hx
  exact mem_rangePow.mpr ⟨t y, by rw [pow_succ, Module.End.mul_apply]⟩

end Chains

section Quotients

/-- The denominator `N_k` of `E_k`, pulled back along the inclusion of `N_(k+1)` into `V`. -/
abbrev kerPowInSucc (k : ℕ) : Submodule R (kerPow t (k + 1)) :=
  (kerPow t k).comap (kerPow t (k + 1)).subtype

/-- The denominator `I_(k+1)` of `F_k`, pulled back along the inclusion of `I_k` into `V`. -/
abbrev rangePowSuccIn (k : ℕ) : Submodule R (rangePow t k) :=
  (rangePow t (k + 1)).comap (rangePow t k).subtype

/-- Renard's `E_k = N_(k+1) / N_k`, an actual quotient module. -/
abbrev KerQuotient (k : ℕ) : Type uV :=
  kerPow t (k + 1) ⧸ kerPowInSucc t k

/-- Renard's `F_k = I_k / I_(k+1)`, an actual quotient module. -/
abbrev RangeQuotient (k : ℕ) : Type uV :=
  rangePow t k ⧸ rangePowSuccIn t k

/-- The canonical projection `N_(k+1) → E_k`. -/
abbrev kerQuotientMk (k : ℕ) : kerPow t (k + 1) →ₗ[R] KerQuotient t k :=
  (kerPowInSucc t k).mkQ

/-- The canonical projection `I_k → F_k`. -/
abbrev rangeQuotientMk (k : ℕ) : rangePow t k →ₗ[R] RangeQuotient t k :=
  (rangePowSuccIn t k).mkQ

variable {t}

theorem mem_kerPowInSucc {k : ℕ} {x : kerPow t (k + 1)} :
    x ∈ kerPowInSucc t k ↔ (x : V) ∈ kerPow t k :=
  Iff.rfl

theorem mem_rangePowSuccIn {k : ℕ} {x : rangePow t k} :
    x ∈ rangePowSuccIn t k ↔ (x : V) ∈ rangePow t (k + 1) :=
  Iff.rfl

variable (t)

/-- The pulled-back denominator of `E_k` is exactly `N_k` inside `V`. -/
theorem map_subtype_kerPowInSucc (k : ℕ) :
    (kerPowInSucc t k).map (kerPow t (k + 1)).subtype = kerPow t k := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr (kerPow_le_succ t k)]

/-- The pulled-back denominator of `F_k` is exactly `I_(k+1)` inside `V`. -/
theorem map_subtype_rangePowSuccIn (k : ℕ) :
    (rangePowSuccIn t k).map (rangePow t k).subtype = rangePow t (k + 1) := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr (rangePow_succ_le t k)]

theorem kerQuotientMk_apply (k : ℕ) (x : kerPow t (k + 1)) :
    kerQuotientMk t k x = Submodule.Quotient.mk x :=
  rfl

theorem rangeQuotientMk_apply (k : ℕ) (x : rangePow t k) :
    rangeQuotientMk t k x = Submodule.Quotient.mk x :=
  rfl

theorem kerQuotientMk_surjective (k : ℕ) : Function.Surjective (kerQuotientMk t k) :=
  Submodule.mkQ_surjective _

theorem rangeQuotientMk_surjective (k : ℕ) : Function.Surjective (rangeQuotientMk t k) :=
  Submodule.mkQ_surjective _

theorem ker_kerQuotientMk (k : ℕ) : LinearMap.ker (kerQuotientMk t k) = kerPowInSucc t k :=
  Submodule.ker_mkQ _

theorem ker_rangeQuotientMk (k : ℕ) :
    LinearMap.ker (rangeQuotientMk t k) = rangePowSuccIn t k :=
  Submodule.ker_mkQ _

variable {t}

theorem kerQuotientMk_eq_zero_iff {k : ℕ} {x : kerPow t (k + 1)} :
    kerQuotientMk t k x = 0 ↔ (x : V) ∈ kerPow t k :=
  Submodule.Quotient.mk_eq_zero _

theorem rangeQuotientMk_eq_zero_iff {k : ℕ} {x : rangePow t k} :
    rangeQuotientMk t k x = 0 ↔ (x : V) ∈ rangePow t (k + 1) :=
  Submodule.Quotient.mk_eq_zero _

end Quotients

section Representatives

/-- The representative map `N_(k+2) → N_(k+1)`, `x ↦ t x`. -/
def kerShift (k : ℕ) : kerPow t (k + 2) →ₗ[R] kerPow t (k + 1) :=
  t.restrict fun _ hx => apply_mem_kerPow hx

/-- The representative map `N_(k+1) → I_k`, `x ↦ t ^ k x`. -/
def kerToRange (k : ℕ) : kerPow t (k + 1) →ₗ[R] rangePow t k :=
  (t ^ k).restrict fun x _ => pow_apply_mem_rangePow k x

/-- The representative map `I_k → I_(k+1)`, `x ↦ t x`. -/
def rangeShift (k : ℕ) : rangePow t k →ₗ[R] rangePow t (k + 1) :=
  t.restrict fun _ hx => apply_mem_rangePow hx

@[simp]
theorem coe_kerShift_apply (k : ℕ) (x : kerPow t (k + 2)) : (kerShift t k x : V) = t x :=
  rfl

@[simp]
theorem coe_kerToRange_apply (k : ℕ) (x : kerPow t (k + 1)) :
    (kerToRange t k x : V) = (t ^ k) x :=
  rfl

@[simp]
theorem coe_rangeShift_apply (k : ℕ) (x : rangePow t k) : (rangeShift t k x : V) = t x :=
  rfl

/-- The source's composite `N_(k+2) → N_(k+1) → N_(k+1) / N_k = E_k`. -/
def kerShiftMk (k : ℕ) : kerPow t (k + 2) →ₗ[R] KerQuotient t k :=
  (kerQuotientMk t k).comp (kerShift t k)

/-- The composite `N_(k+1) → I_k → I_k / I_(k+1) = F_k` of `t ^ k` with the projection. -/
def kerToRangeMk (k : ℕ) : kerPow t (k + 1) →ₗ[R] RangeQuotient t k :=
  (rangeQuotientMk t k).comp (kerToRange t k)

/-- The source's composite `I_k → I_(k+1) → I_(k+1) / I_(k+2) = F_(k+1)`. -/
def rangeShiftMk (k : ℕ) : rangePow t k →ₗ[R] RangeQuotient t (k + 1) :=
  (rangeQuotientMk t (k + 1)).comp (rangeShift t k)

theorem kerShiftMk_apply (k : ℕ) (x : kerPow t (k + 2)) :
    kerShiftMk t k x = kerQuotientMk t k (kerShift t k x) :=
  rfl

theorem kerToRangeMk_apply (k : ℕ) (x : kerPow t (k + 1)) :
    kerToRangeMk t k x = rangeQuotientMk t k (kerToRange t k x) :=
  rfl

theorem rangeShiftMk_apply (k : ℕ) (x : rangePow t k) :
    rangeShiftMk t k x = rangeQuotientMk t (k + 1) (rangeShift t k x) :=
  rfl

/-- The composite `N_(k+2) → E_k` vanishes on `N_(k+1)`, the denominator of `E_(k+1)`. -/
theorem kerPowInSucc_le_ker_kerShiftMk (k : ℕ) :
    kerPowInSucc t (k + 1) ≤ LinearMap.ker (kerShiftMk t k) := by
  intro x hx
  rw [LinearMap.mem_ker, kerShiftMk_apply, kerQuotientMk_eq_zero_iff, coe_kerShift_apply]
  exact apply_mem_kerPow (mem_kerPowInSucc.mp hx)

/-- The restriction of `t ^ k` to `N_(k+1)` vanishes on `N_k`. -/
theorem kerPowInSucc_le_ker_kerToRange (k : ℕ) :
    kerPowInSucc t k ≤ LinearMap.ker (kerToRange t k) := by
  intro x hx
  rw [LinearMap.mem_ker, ← Subtype.coe_inj, coe_kerToRange_apply, Submodule.coe_zero]
  exact mem_kerPow.mp (mem_kerPowInSucc.mp hx)

/-- Hence the composite `N_(k+1) → F_k` vanishes on `N_k`, the denominator of `E_k`. -/
theorem kerPowInSucc_le_ker_kerToRangeMk (k : ℕ) :
    kerPowInSucc t k ≤ LinearMap.ker (kerToRangeMk t k) :=
  (kerPowInSucc_le_ker_kerToRange t k).trans (LinearMap.ker_le_ker_comp _ _)

/-- The composite `I_k → F_(k+1)` vanishes on `I_(k+1)`, the denominator of `F_k`. -/
theorem rangePowSuccIn_le_ker_rangeShiftMk (k : ℕ) :
    rangePowSuccIn t k ≤ LinearMap.ker (rangeShiftMk t k) := by
  intro x hx
  rw [LinearMap.mem_ker, rangeShiftMk_apply, rangeQuotientMk_eq_zero_iff, coe_rangeShift_apply]
  exact apply_mem_rangePow (mem_rangePowSuccIn.mp hx)

end Representatives

section Arrows

/-- The arrow `E_(k+1) → E_k` induced by `t`, descended from `kerShiftMk`. -/
def kerQuotientShift (k : ℕ) : KerQuotient t (k + 1) →ₗ[R] KerQuotient t k :=
  (kerPowInSucc t (k + 1)).liftQ (kerShiftMk t k) (kerPowInSucc_le_ker_kerShiftMk t k)

/-- The arrow `E_k → F_k` induced by `t ^ k`, descended from `kerToRangeMk`. -/
def kerToRangeQuotient (k : ℕ) : KerQuotient t k →ₗ[R] RangeQuotient t k :=
  (kerPowInSucc t k).liftQ (kerToRangeMk t k) (kerPowInSucc_le_ker_kerToRangeMk t k)

/-- The arrow `F_k → F_(k+1)` induced by `t`, descended from `rangeShiftMk`. -/
def rangeQuotientShift (k : ℕ) : RangeQuotient t k →ₗ[R] RangeQuotient t (k + 1) :=
  (rangePowSuccIn t k).liftQ (rangeShiftMk t k) (rangePowSuccIn_le_ker_rangeShiftMk t k)

theorem kerQuotientShift_mk (k : ℕ) (x : kerPow t (k + 2)) :
    kerQuotientShift t k (kerQuotientMk t (k + 1) x) = kerQuotientMk t k (kerShift t k x) :=
  rfl

theorem kerToRangeQuotient_mk (k : ℕ) (x : kerPow t (k + 1)) :
    kerToRangeQuotient t k (kerQuotientMk t k x) = rangeQuotientMk t k (kerToRange t k x) :=
  rfl

theorem rangeQuotientShift_mk (k : ℕ) (x : rangePow t k) :
    rangeQuotientShift t k (rangeQuotientMk t k x) =
      rangeQuotientMk t (k + 1) (rangeShift t k x) :=
  rfl

/-- `kerQuotientShift_mk` in `simp` normal form, where the projection is unfolded. -/
@[simp]
theorem kerQuotientShift_quotient_mk (k : ℕ) (x : kerPow t (k + 2)) :
    kerQuotientShift t k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (kerShift t k x) :=
  rfl

/-- `kerToRangeQuotient_mk` in `simp` normal form, where the projection is unfolded. -/
@[simp]
theorem kerToRangeQuotient_quotient_mk (k : ℕ) (x : kerPow t (k + 1)) :
    kerToRangeQuotient t k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (kerToRange t k x) :=
  rfl

/-- `rangeQuotientShift_mk` in `simp` normal form, where the projection is unfolded. -/
@[simp]
theorem rangeQuotientShift_quotient_mk (k : ℕ) (x : rangePow t k) :
    rangeQuotientShift t k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (rangeShift t k x) :=
  rfl

theorem kerQuotientShift_comp_mk (k : ℕ) :
    (kerQuotientShift t k).comp (kerQuotientMk t (k + 1)) = kerShiftMk t k :=
  Submodule.liftQ_mkQ _ _ _

theorem kerToRangeQuotient_comp_mk (k : ℕ) :
    (kerToRangeQuotient t k).comp (kerQuotientMk t k) = kerToRangeMk t k :=
  Submodule.liftQ_mkQ _ _ _

theorem rangeQuotientShift_comp_mk (k : ℕ) :
    (rangeQuotientShift t k).comp (rangeQuotientMk t k) = rangeShiftMk t k :=
  Submodule.liftQ_mkQ _ _ _

/-- `kerShift` maps the denominator `N_(k+1)` of `E_(k+1)` into the denominator `N_k` of `E_k`. -/
theorem kerPowInSucc_le_comap_kerShift (k : ℕ) :
    kerPowInSucc t (k + 1) ≤ (kerPowInSucc t k).comap (kerShift t k) :=
  fun _ hx => apply_mem_kerPow (mem_kerPowInSucc.mp hx)

/-- `kerToRange` maps the denominator `N_k` of `E_k` into the denominator `I_(k+1)` of `F_k`. -/
theorem kerPowInSucc_le_comap_kerToRange (k : ℕ) :
    kerPowInSucc t k ≤ (rangePowSuccIn t k).comap (kerToRange t k) := by
  intro x hx
  rw [Submodule.mem_comap, mem_rangePowSuccIn, coe_kerToRange_apply,
    mem_kerPow.mp (mem_kerPowInSucc.mp hx)]
  exact Submodule.zero_mem _

/-- `rangeShift` maps the denominator `I_(k+1)` of `F_k` into the denominator `I_(k+2)` of
`F_(k+1)`. -/
theorem rangePowSuccIn_le_comap_rangeShift (k : ℕ) :
    rangePowSuccIn t k ≤ (rangePowSuccIn t (k + 1)).comap (rangeShift t k) :=
  fun _ hx => apply_mem_rangePow (mem_rangePowSuccIn.mp hx)

/-- The first arrow is Mathlib's `mapQ` of `kerShift`. -/
theorem kerQuotientShift_eq_mapQ (k : ℕ) :
    kerQuotientShift t k =
      (kerPowInSucc t (k + 1)).mapQ (kerPowInSucc t k) (kerShift t k)
        (kerPowInSucc_le_comap_kerShift t k) :=
  rfl

/-- The middle arrow is Mathlib's `mapQ` of `kerToRange`. -/
theorem kerToRangeQuotient_eq_mapQ (k : ℕ) :
    kerToRangeQuotient t k =
      (kerPowInSucc t k).mapQ (rangePowSuccIn t k) (kerToRange t k)
        (kerPowInSucc_le_comap_kerToRange t k) :=
  rfl

/-- The last arrow is Mathlib's `mapQ` of `rangeShift`. -/
theorem rangeQuotientShift_eq_mapQ (k : ℕ) :
    rangeQuotientShift t k =
      (rangePowSuccIn t k).mapQ (rangePowSuccIn t (k + 1)) (rangeShift t k)
        (rangePowSuccIn_le_comap_rangeShift t k) :=
  rfl

/-- Representative formula `[x] ↦ [t x]` for `E_(k+1) → E_k`. -/
theorem kerQuotientShift_mk_mk (k : ℕ) (x : V) (hx : x ∈ kerPow t (k + 2))
    (htx : t x ∈ kerPow t (k + 1)) :
    kerQuotientShift t k (kerQuotientMk t (k + 1) ⟨x, hx⟩) = kerQuotientMk t k ⟨t x, htx⟩ :=
  rfl

/-- Representative formula `[x] ↦ [t ^ k x]` for `E_k → F_k`. -/
theorem kerToRangeQuotient_mk_mk (k : ℕ) (x : V) (hx : x ∈ kerPow t (k + 1))
    (htx : (t ^ k) x ∈ rangePow t k) :
    kerToRangeQuotient t k (kerQuotientMk t k ⟨x, hx⟩) = rangeQuotientMk t k ⟨(t ^ k) x, htx⟩ :=
  rfl

/-- Representative formula `[x] ↦ [t x]` for `F_k → F_(k+1)`. -/
theorem rangeQuotientShift_mk_mk (k : ℕ) (x : V) (hx : x ∈ rangePow t k)
    (htx : t x ∈ rangePow t (k + 1)) :
    rangeQuotientShift t k (rangeQuotientMk t k ⟨x, hx⟩) =
      rangeQuotientMk t (k + 1) ⟨t x, htx⟩ :=
  rfl

end Arrows

section ComplexSpecialization

/-! The case of Renard's text: an arbitrary complex vector space, with no finiteness
hypothesis, and every natural index `k`, including `k = 0`. -/

variable {W : Type uV} [AddCommGroup W] [Module ℂ W] (s : Module.End ℂ W) (k : ℕ)

example : Module ℂ (KerQuotient s k) := inferInstance

example : Module ℂ (RangeQuotient s k) := inferInstance

example : kerPow s (k + 1) →ₗ[ℂ] KerQuotient s k := kerQuotientMk s k

example : rangePow s k →ₗ[ℂ] RangeQuotient s k := rangeQuotientMk s k

example : KerQuotient s (k + 1) →ₗ[ℂ] KerQuotient s k := kerQuotientShift s k

example : KerQuotient s k →ₗ[ℂ] RangeQuotient s k := kerToRangeQuotient s k

example : RangeQuotient s k →ₗ[ℂ] RangeQuotient s (k + 1) := rangeQuotientShift s k

example : kerPow s 0 = ⊥ ∧ rangePow s 0 = ⊤ := ⟨kerPow_zero s, rangePow_zero s⟩

example (x : kerPow s (k + 2)) :
    kerQuotientShift s k (kerQuotientMk s (k + 1) x) = kerQuotientMk s k (kerShift s k x) := by
  simp

example (x : kerPow s (k + 1)) :
    kerToRangeQuotient s k (kerQuotientMk s k x) = rangeQuotientMk s k (kerToRange s k x) := by
  simp

example (x : rangePow s k) :
    rangeQuotientShift s k (rangeQuotientMk s k x) =
      rangeQuotientMk s (k + 1) (rangeShift s k x) := by
  simp

end ComplexSpecialization

end Langlands.LinearAlgebra.StableEndomorphism
