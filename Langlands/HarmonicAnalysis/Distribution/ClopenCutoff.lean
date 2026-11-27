import Langlands.HarmonicAnalysis.Distribution.Subspace

/-! # Clopen cutoff of a distribution on an open subspace -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open Function Set Topology
open Hecke.TestFunction (pullback pullback_apply)

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] {U C : Set X}

private def cutoffHomeomorph (hCU : C ⊆ U) : (Subtype.val ⁻¹' C : Set U) ≃ₜ C where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hCU x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_inclusion hCU).subtype_mk _

namespace SchwartzBruhat

/-- Restrict a test to `C`, transfer it to its copy in `U`, and extend it by zero on `U`. -/
def clopenCutoff (hC : IsClopen C) (hCU : C ⊆ U) : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat U :=
  (extendZero (hC.2.preimage (continuous_subtype_val : Continuous (Subtype.val : U → X)))).comp
    ((pullback (cutoffHomeomorph hCU)).toLinearMap.comp (restrictClosed hC.1))

@[simp]
theorem clopenCutoff_apply_of_mem (hC : IsClopen C) (hCU : C ⊆ U) (f : SchwartzBruhat X)
    (x : U) (hx : x.val ∈ C) : clopenCutoff hC hCU f x = f x.val := by
  unfold clopenCutoff
  rw [LinearMap.comp_apply,
    extendZero_apply_of_mem _ _ (show x ∈ (Subtype.val ⁻¹' C : Set U) from hx)]
  rfl

@[simp]
theorem clopenCutoff_apply_of_not_mem (hC : IsClopen C) (hCU : C ⊆ U) (f : SchwartzBruhat X)
    (x : U) (hx : x.val ∉ C) : clopenCutoff hC hCU f x = 0 := by
  unfold clopenCutoff
  rw [LinearMap.comp_apply,
    extendZero_apply_of_not_mem _ _ (show x ∉ (Subtype.val ⁻¹' C : Set U) from hx)]

end SchwartzBruhat

namespace Distribution

/-- For a distribution on `U`, keep its restriction to `C` and set it to zero off `C`. -/
def clopenCutoff (hC : IsClopen C) (hCU : C ⊆ U) (T : Distribution U) : Distribution X :=
  T.comp (SchwartzBruhat.clopenCutoff hC hCU)

/-- Restriction to a clopen subset followed by extension preserves tests supported there,
annihilates tests vanishing there, and commutes with compatible symmetries. -/
def ClopenCutoffStatement (hC : IsClopen C) (hCU : C ⊆ U) (T : Distribution U) : Prop :=
  clopenCutoff hC hCU T ∈ supportedOn C ∧
    (∀ (hU : IsOpen U) (f : SchwartzBruhat U),
      support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
      clopenCutoff hC hCU T (SchwartzBruhat.extendZero hU f) = T f) ∧
    ∀ (e : X ≃ₜ X) (eU : U ≃ₜ U),
      (∀ x : U, (eU x).val = e x.val) → (∀ x : X, x ∈ C ↔ e x ∈ C) →
      pushforward e (clopenCutoff hC hCU T) = clopenCutoff hC hCU (pushforward eU T)

theorem clopenCutoff_spec (hC : IsClopen C) (hCU : C ⊆ U) (T : Distribution U) :
    ClopenCutoffStatement hC hCU T := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    change T (SchwartzBruhat.clopenCutoff hC hCU f) = 0
    have hzero : SchwartzBruhat.clopenCutoff hC hCU f = 0 := by
      ext x
      by_cases hx : x.val ∈ C
      · simp [hx, hf x.val hx]
      · simp [hx]
    rw [hzero, map_zero]
  · intro hU f hf
    change T (SchwartzBruhat.clopenCutoff hC hCU (SchwartzBruhat.extendZero hU f)) = T f
    congr 1
    ext x
    by_cases hx : x.val ∈ C
    · simp [hx]
    · rw [SchwartzBruhat.clopenCutoff_apply_of_not_mem _ _ _ _ hx]
      exact notMem_support.mp (fun h => hx (hf h)) |>.symm
  · intro e eU he hCinv
    ext f
    change T (SchwartzBruhat.clopenCutoff hC hCU (pullback e f)) =
      T (pullback eU (SchwartzBruhat.clopenCutoff hC hCU f))
    congr 1
    ext x
    rw [pullback_apply]
    by_cases hx : x.val ∈ C
    · have hx' : (eU x).val ∈ C := by rw [he]; exact (hCinv _).1 hx
      rw [SchwartzBruhat.clopenCutoff_apply_of_mem _ _ _ _ hx,
        SchwartzBruhat.clopenCutoff_apply_of_mem _ _ _ _ hx', pullback_apply, he]
    · have hx' : (eU x).val ∉ C := by rw [he]; exact (hCinv _).not.mp hx
      simp [hx, hx']

end Distribution

end Langlands.HarmonicAnalysis

namespace Langlands.Whittaker.BruhatCompatibleSupport

open Langlands.HarmonicAnalysis

variable {X : Type*} [TopologicalSpace X]

/-- The product of a test function with the indicator function of a clopen set. -/
def clopenCutoff {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun x => LocallyConstant.charFn ℂ hV x * f x,
    (LocallyConstant.charFn ℂ hV).isLocallyConstant.comp₂ f.locallyConstant (· * ·),
    f.hasCompactSupport.mul_left⟩

theorem clopenCutoff_apply_of_mem {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X)
    {x : X} (hx : x ∈ V) : clopenCutoff hV f x = f x := by
  change V.indicator (fun _ => (1 : ℂ)) x * f x = f x
  rw [Set.indicator_of_mem hx, one_mul]

theorem clopenCutoff_apply_of_notMem {V : Set X} (hV : IsClopen V) (f : SchwartzBruhat X)
    {x : X} (hx : x ∉ V) : clopenCutoff hV f x = 0 := by
  change V.indicator (fun _ => (1 : ℂ)) x * f x = 0
  rw [Set.indicator_of_notMem hx, zero_mul]

end Langlands.Whittaker.BruhatCompatibleSupport
