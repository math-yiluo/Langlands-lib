import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! # The telescope resolution of an increasing sequence of submodules -/

universe u v

namespace Langlands.CommutativeAlgebra

open CategoryTheory DirectSum

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

variable (F : ℕ → Submodule R M) (hF : Monotone F)

/-- Shift along the inclusions of an increasing sequence of submodules. -/
noncomputable def sequentialSubmoduleShift : (⨁ n, F n) →ₗ[R] ⨁ n, F n :=
  DirectSum.toModule R ℕ _ fun n =>
    (DirectSum.lof R ℕ (fun n => F n) (n + 1)).comp
      (Submodule.inclusion (hF (Nat.le_succ n)))

/-- The telescope differential, identity minus the transition shift. -/
noncomputable def sequentialSubmoduleDifference : (⨁ n, F n) →ₗ[R] ⨁ n, F n :=
  LinearMap.id - sequentialSubmoduleShift F hF

@[simp]
theorem sequentialSubmoduleShift_lof (n : ℕ) (x : F n) :
    sequentialSubmoduleShift F hF (DirectSum.lof R ℕ (fun n => F n) n x) =
      DirectSum.lof R ℕ (fun n => F n) (n + 1)
        (Submodule.inclusion (hF (Nat.le_succ n)) x) := by
  simp [sequentialSubmoduleShift]

@[simp]
theorem sequentialSubmoduleShift_zero (p : ⨁ n, F n) :
    sequentialSubmoduleShift F hF p 0 = 0 := by
  induction p using DirectSum.induction_on with
  | zero => simp
  | of n x =>
    change sequentialSubmoduleShift F hF (DirectSum.lof R ℕ (fun n => F n) n x) 0 = 0
    rw [sequentialSubmoduleShift_lof]
    exact DirectSum.of_eq_of_ne (n + 1) 0 _ (by omega)
  | add p q hp hq => simp [hp, hq]

@[simp]
theorem sequentialSubmoduleShift_succ (p : ⨁ n, F n) (n : ℕ) :
    sequentialSubmoduleShift F hF p (n + 1) =
      Submodule.inclusion (hF (Nat.le_succ n)) (p n) := by
  induction p using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change sequentialSubmoduleShift F hF (DirectSum.lof R ℕ (fun n => F n) i x) (n + 1) =
      Submodule.inclusion (hF (Nat.le_succ n)) (DirectSum.of (fun n => F n) i x n)
    rw [sequentialSubmoduleShift_lof]
    change DirectSum.of (fun n => F n) (i + 1) _ (n + 1) = _
    by_cases hi : i = n
    · subst i
      simp
    · simp [DirectSum.of_apply, hi]
  | add p q hp hq => simp [hp, hq]

theorem sequentialSubmoduleDifference_injective :
    Function.Injective (sequentialSubmoduleDifference F hF) := by
  apply (injective_iff_map_eq_zero _).2
  intro p hp
  apply DFinsupp.ext
  intro n
  change p n = 0
  induction n with
  | zero =>
    have := congrArg (fun q : ⨁ n, F n => q 0) hp
    simpa [sequentialSubmoduleDifference] using this
  | succ n ih =>
    have := congrArg (fun q : ⨁ n, F n => q (n + 1)) hp
    simpa [sequentialSubmoduleDifference, ih] using this

theorem sequentialSubmodule_coeLinearMap_difference :
    (DirectSum.coeLinearMap F).comp (sequentialSubmoduleDifference F hF) = 0 := by
  apply DirectSum.linearMap_ext
  intro n
  ext x
  simp [sequentialSubmoduleDifference]

theorem sequentialSubmodule_lof_sub_lof_mem_range (i j : ℕ) (hij : i ≤ j) (x : F i) :
    DirectSum.lof R ℕ (fun n => F n) i x -
      DirectSum.lof R ℕ (fun n => F n) j (Submodule.inclusion (hF hij) x) ∈
        LinearMap.range (sequentialSubmoduleDifference F hF) := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    change DirectSum.lof R ℕ (fun n => F n) 0 x -
      DirectSum.lof R ℕ (fun n => F n) 0 x ∈ _
    simp only [sub_self]
    exact Submodule.zero_mem _
  | succ j ih =>
    by_cases hi : i ≤ j
    · have h₁ := ih hi
      have h₂ : DirectSum.lof R ℕ (fun n => F n) j
            (Submodule.inclusion (hF hi) x) -
          DirectSum.lof R ℕ (fun n => F n) (j + 1)
            (Submodule.inclusion (hF hij) x) ∈
          LinearMap.range (sequentialSubmoduleDifference F hF) := by
        refine ⟨DirectSum.lof R ℕ (fun n => F n) j
          (Submodule.inclusion (hF hi) x), ?_⟩
        simp [sequentialSubmoduleDifference]
        rfl
      simpa only [sub_add_sub_cancel] using
        (LinearMap.range (sequentialSubmoduleDifference F hF)).add_mem h₁ h₂
    · have hi' : i = j + 1 := by omega
      subst i
      change DirectSum.lof R ℕ (fun n => F n) (j + 1) x -
        DirectSum.lof R ℕ (fun n => F n) (j + 1) x ∈ _
      simp only [sub_self]
      exact Submodule.zero_mem _

/-- Every finite sum is congruent modulo telescope differences to one later summand. -/
theorem sequentialSubmodule_normalForm (p : ⨁ n, F n) :
    ∃ (n : ℕ) (x : F n),
      p - DirectSum.lof R ℕ (fun n => F n) n x ∈
          LinearMap.range (sequentialSubmoduleDifference F hF) ∧
        (x : M) = DirectSum.coeLinearMap F p := by
  classical
  induction p using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | of n x => exact ⟨n, x, by simp [DirectSum.lof_eq_of], by simp⟩
  | add p q hp hq =>
    obtain ⟨i, x, hx, hxp⟩ := hp
    obtain ⟨j, y, hy, hyq⟩ := hq
    let k := max i j
    let x' : F k := Submodule.inclusion (hF (le_max_left i j)) x
    let y' : F k := Submodule.inclusion (hF (le_max_right i j)) y
    have hx' := sequentialSubmodule_lof_sub_lof_mem_range F hF i k (le_max_left i j) x
    have hy' := sequentialSubmodule_lof_sub_lof_mem_range F hF j k (le_max_right i j) y
    refine ⟨k, x' + y', ?_, ?_⟩
    · have hr := (LinearMap.range (sequentialSubmoduleDifference F hF)).add_mem
        ((LinearMap.range (sequentialSubmoduleDifference F hF)).add_mem hx hx')
        ((LinearMap.range (sequentialSubmoduleDifference F hF)).add_mem hy hy')
      convert hr using 1
      simp only [map_add, sub_add_sub_cancel]
      abel
    · simp [x', y', hxp, hyq]

theorem sequentialSubmoduleDifference_range_eq_ker :
    LinearMap.range (sequentialSubmoduleDifference F hF) =
      LinearMap.ker (DirectSum.coeLinearMap F) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change DirectSum.coeLinearMap F (sequentialSubmoduleDifference F hF p) = 0
    exact DFunLike.congr_fun (sequentialSubmodule_coeLinearMap_difference F hF) p
  · intro p hp
    obtain ⟨n, x, hx, hxp⟩ := sequentialSubmodule_normalForm F hF p
    have hx0 : x = 0 := Subtype.ext (hxp.trans hp)
    simpa [hx0] using hx

/-- The actual telescope complex for an increasing sequence of submodules. -/
noncomputable def sequentialSubmoduleShortComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (sequentialSubmoduleDifference F hF)
    (DirectSum.coeLinearMap F) (sequentialSubmodule_coeLinearMap_difference F hF)

theorem sequentialSubmoduleShortComplex_shortExact (hcover : iSup F = ⊤) :
    (sequentialSubmoduleShortComplex F hF).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact LinearMap.exact_iff.2 (sequentialSubmoduleDifference_range_eq_ker F hF).symm
  · exact sequentialSubmoduleDifference_injective F hF
  · exact LinearMap.range_eq_top.1 ((DirectSum.range_coeLinearMap (A := F)).trans hcover)

include hF in
/-- A module exhausted by an increasing sequence of projective submodules has dimension at most one. -/
theorem hasProjectiveDimensionLE_one_of_sequential_projective_submodules
    [∀ n, Module.Projective R (F n)] (hcover : iSup F = ⊤) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 1 := by
  have h₁ : HasProjectiveDimensionLT (ModuleCat.of R (⨁ n, F n)) 1 := inferInstance
  have h₂ : HasProjectiveDimensionLT (ModuleCat.of R (⨁ n, F n)) 2 := inferInstance
  exact (sequentialSubmoduleShortComplex_shortExact F hF hcover).hasProjectiveDimensionLT_X₃
    1 h₁ h₂

end Langlands.CommutativeAlgebra
