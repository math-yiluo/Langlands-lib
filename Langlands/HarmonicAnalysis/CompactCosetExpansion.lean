import Langlands.HarmonicAnalysis.Basic
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Finite sampled-value Schwartz expansions of uniformly locally constant families. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe uX uA

/-- Finite Schwartz functions and sample points reconstructing an entire family. -/
structure FiniteSchwartzExpansion
    {X : Type uX} [TopologicalSpace X] {A : Type uA} (H : X → A → ℂ) where
  size : ℕ
  functions : Fin size → SchwartzBruhat X
  samples : Fin size → X
  expansion : ∀ a x, H x a = ∑ i : Fin size, functions i x * H (samples i) a

/-- A uniformly locally constant, compactly supported family has a finite
Schwartz expansion whose coefficients are values of that same family.
All finite data are chosen independently of both the parameter and the point. -/
theorem exists_finite_schwartz_expansion
    {X : Type uX} [TopologicalSpace X] {A : Type uA} (H : X → A → ℂ)
    (hH : IsLocallyConstant H) (hC : HasCompactSupport H) :
    ∃ (m : ℕ) (φ : Fin m → SchwartzBruhat X) (r : Fin m → X),
      ∀ a x, H x a = ∑ i : Fin m, φ i x * H (r i) a := by
  classical
  let S : Set (A → ℂ) := {v | v ∈ Set.range H ∧ v ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport hH hC).subset
      (fun _ hv => hv.1)
  let : Fintype S := hS.fintype
  let r : S → X := fun v => Classical.choose v.property.1
  have hr (v : S) : H (r v) = v.val := Classical.choose_spec v.property.1
  let φ : S → SchwartzBruhat X := fun v =>
    ⟨fun x => if H x = v.val then 1 else 0,
      hH.comp (fun w => if w = v.val then (1 : ℂ) else 0),
      hC.comp_left (g := fun w => if w = v.val then (1 : ℂ) else 0)
        (by simp [Ne.symm v.property.2])⟩
  have hsum (a : A) (x : X) : H x a = ∑ v : S, φ v x * H (r v) a := by
    by_cases hx : H x = 0
    · have he (v : S) : (0 : A → ℂ) ≠ v.val := Ne.symm v.property.2
      simp [φ, he, hx]
    · let v : S := ⟨H x, ⟨⟨x, rfl⟩, hx⟩⟩
      rw [Finset.sum_eq_single v]
      · simp [φ, hr, v]
      · intro w _ hw
        have he : H x ≠ w.val := by
          intro h
          exact hw (Subtype.ext h.symm)
        simp [φ, he]
      · simp
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, fun i => φ (e.symm i), fun i => r (e.symm i), ?_⟩
  intro a x
  rw [hsum a x]
  exact Fintype.sum_equiv e _ _ (fun v => by simp)

/-- Choose finite expansion data from uniform local constancy and compact support. -/
def finiteSchwartzExpansion
    {X : Type uX} [TopologicalSpace X] {A : Type uA} (H : X → A → ℂ)
    (hH : IsLocallyConstant H) (hC : HasCompactSupport H) :
    FiniteSchwartzExpansion H :=
  Classical.choice (by
    obtain ⟨m, φ, r, h⟩ := exists_finite_schwartz_expansion H hH hC
    exact ⟨{ size := m, functions := φ, samples := r, expansion := h }⟩)

/-- A family invariant under an open additive subgroup and supported in one
compact set has a common finite sampled-value Schwartz expansion.
The compactness of the subgroup is retained for the compact-open interface. -/
theorem exists_compactCosetExpansion
    {X : Type uX} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] {A : Type uA}
    (U : OpenAddSubgroup X) (_hU : IsCompact (U : Set X)) (H : A → X → ℂ)
    (hinv : ∀ a x u, u ∈ U → H a (x + u) = H a x)
    (hsupp : ∃ C : Set X, IsCompact C ∧ ∀ a x, H a x ≠ 0 → x ∈ C) :
    ∃ (m : ℕ) (φ : Fin m → SchwartzBruhat X) (r : Fin m → X),
      ∀ a x, H a x = ∑ i : Fin m, φ i x * H a (r i) := by
  have hH : IsLocallyConstant (fun x a => H a x) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hneigh : {y : X | y - x ∈ U} ∈ nhds x :=
      (U.isOpen.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simp)
    filter_upwards [hneigh] with y hy
    funext a
    simpa [add_comm, sub_eq_add_neg, add_assoc] using hinv a x (y - x) hy
  have hC : HasCompactSupport (fun x a => H a x) := by
    obtain ⟨C, hC, hsupport⟩ := hsupp
    apply HasCompactSupport.intro hC
    intro x hx
    funext a
    by_contra h
    exact hx (hsupport a x h)
  exact exists_finite_schwartz_expansion (fun x a => H a x) hH hC

end Langlands.HarmonicAnalysis
