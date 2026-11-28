import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Basic.Complex.Basic

/-! # Closed range of a sufficiently high jet with a scaled inverse -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.HigherJetClosedRange

universe u v

section Preimage

variable {E : Type u} {F : Type v} [AddCommGroup E] [Module ℂ E]
  [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- The two scaled inverse identities identify the image with a preimage if the target
scaling has kernel contained in its range. -/
theorem range_eq_preimage (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hST : ∀ x, S (T x) = A x) (hTS : ∀ y, T (S y) = B y)
    (hB : ∀ y, B y = 0 → y ∈ Set.range B) :
    Set.range T = S ⁻¹' Set.range A := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (hST x).symm⟩
  · rintro ⟨x, hx⟩
    have hzero : S (y - T x) = 0 := by rw [map_sub, hST, hx, sub_self]
    have hBzero : B (y - T x) = 0 := by rw [← hTS, hzero, map_zero]
    obtain ⟨z, hz⟩ := hB _ hBzero
    refine ⟨x + S z, ?_⟩
    rw [map_add, hTS, hz, add_sub_cancel]

/-- A split projection takes the image to a closed subspace exactly when the image plus
the kernel of the projection is closed upstairs. -/
theorem isClosed_range_comp_iff_of_rightInverse {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (T : E →L[ℂ] F) (P : F →L[ℂ] G) (s : G →L[ℂ] F)
    (hs : Function.RightInverse s P) :
    IsClosed (Set.range (P.comp T)) ↔
      IsClosed ((T.toLinearMap.range ⊔ P.toLinearMap.ker : Submodule ℂ F) : Set F) := by
  have he : P ⁻¹' Set.range (P.comp T) =
      ((T.toLinearMap.range ⊔ P.toLinearMap.ker : Submodule ℂ F) : Set F) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_range, ContinuousLinearMap.comp_apply,
      SetLike.mem_coe, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx⟩
      have hzero : P.toLinearMap (y - T x) = 0 := by
        change P (y - T x) = 0
        rw [map_sub, hx, sub_self]
      exact ⟨T x, ⟨x, rfl⟩, y - T x, LinearMap.mem_ker.mpr hzero, add_sub_cancel _ _⟩
    · rintro ⟨z, ⟨x, rfl⟩, w, hw, rfl⟩
      have hw₀ : P w = 0 := LinearMap.mem_ker.mp hw
      refine ⟨x, ?_⟩
      rw [map_add, hw₀, add_zero]
      rfl
  constructor
  · intro h
    rw [← he]
    exact h.preimage P.continuous
  · rw [← he]
    intro h
    have hs' : s ⁻¹' (P ⁻¹' Set.range (P.comp T)) = Set.range (P.comp T) := by
      ext z
      simp only [Set.mem_preimage, hs z]
    rw [← hs']
    exact h.preimage s.continuous

end Preimage

section Coordinates

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Multiplication by the parameter to the `k`th power on an `m`-jet in coefficient
coordinates, truncated at degree `m`. -/
def shift (m k : ℕ) : (Fin m → E) →L[ℂ] (Fin m → E) :=
  ContinuousLinearMap.pi fun i =>
    if h : k ≤ i.val then ContinuousLinearMap.proj (R := ℂ) (⟨i.val - k, by omega⟩ : Fin m)
    else 0

theorem shift_apply_of_le {m k : ℕ} (x : Fin m → E) (i : Fin m) (h : k ≤ i.val) :
    shift m k x i = x ⟨i.val - k, by omega⟩ := by
  simp only [shift, ContinuousLinearMap.pi_apply, dite_eq_left h, ContinuousLinearMap.proj_apply]

theorem shift_apply_of_lt {m k : ℕ} (x : Fin m → E) (i : Fin m) (h : i.val < k) :
    shift m k x i = 0 := by
  simp only [shift, ContinuousLinearMap.pi_apply, dite_eq_right (not_le.mpr h), zero_apply]

/-- The image of the parameter shift consists of the jets whose first `k` coefficients vanish. -/
theorem range_shift (m k : ℕ) :
    Set.range (shift (E := E) m k) = {x : Fin m → E | ∀ i : Fin m, i.val < k → x i = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact shift_apply_of_lt y i hi
  · intro hx
    let y (i : Fin m) := if h : i.val + k < m then x ⟨i.val + k, h⟩ else 0
    refine ⟨y, funext fun i => ?_⟩
    by_cases hi : k ≤ i.val
    · rw [shift_apply_of_le y i hi]
      have he : i.val - k + k = i.val := by omega
      have h : i.val - k + k < m := by omega
      simp only [y, dite_eq_left h]
      congr 1
      exact Fin.ext he
    · have hlt : i.val < k := Nat.lt_of_not_ge hi
      exact (shift_apply_of_lt y i hlt).trans (hx i hlt).symm

/-- For `m ≥ 2k`, every jet killed by the shift has its first `k` coefficients zero. -/
theorem mem_range_shift_of_shift_eq_zero {m k : ℕ} (hm : 2 * k ≤ m)
    (x : Fin m → E) (hx : shift m k x = 0) : x ∈ Set.range (shift (E := E) m k) := by
  rw [range_shift]
  intro i hi
  let j : Fin m := ⟨i.val + k, by omega⟩
  have hj : k ≤ j.val := by dsimp only [j]; omega
  have h := congrFun hx j
  rw [shift_apply_of_le x j hj] at h
  have he : (⟨j.val - k, by omega⟩ : Fin m) = i := by apply Fin.ext; dsimp only [j]; omega
  rwa [he] at h

variable [T2Space E]

theorem isClosed_range_shift (m k : ℕ) : IsClosed (Set.range (shift (E := E) m k)) := by
  rw [range_shift]
  have he : {x : Fin m → E | ∀ i : Fin m, i.val < k → x i = 0} =
      ⋂ i : Fin m, ⋂ _ : i.val < k, (fun x : Fin m → E => x i) ⁻¹' {0} := by
    ext x
    simp
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (continuous_apply i)

end Coordinates

/-- If two continuous maps between coefficient jet spaces compose in both orders to the
`k`th parameter shift, the forward map has closed range when the jet length is at least `2k`. -/
def HigherJetClosedRangeStatement : Prop :=
  ∀ {E : Type u} {F : Type v} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (m k : ℕ), 2 * k ≤ m →
    ∀ (T : (Fin m → E) →L[ℂ] (Fin m → F)) (S : (Fin m → F) →L[ℂ] (Fin m → E)),
      (∀ x, S (T x) = shift m k x) → (∀ y, T (S y) = shift m k y) → IsClosed (Set.range T)

theorem higherJetClosedRange : HigherJetClosedRangeStatement.{u, v} := by
  intro E F _ _ _ _ _ _ _ m k hm T S hST hTS
  rw [range_eq_preimage T S (shift m k) (shift m k) hST hTS
    (mem_range_shift_of_shift_eq_zero hm)]
  exact (isClosed_range_shift m k).preimage S.continuous

end Langlands.Archimedean.HigherJetClosedRange
