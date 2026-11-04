import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Projections onto graded subspaces that respect the grading -/

noncomputable section

universe u

namespace Langlands.GroupScheme.TorusLinearization

section GradedProjection

variable {K V M : Type u} [Field K] [AddCommGroup V] [Module K V] [DecidableEq M]
  {c : M → V →ₗ[K] V}

/-- A vector in the image of a component projection is killed by the other components
and fixed by its own. -/
theorem graded_apply_of_mem_range
    (hcc : ∀ χ ψ v, c ψ (c χ v) = if χ = ψ then c χ v else 0) {ψ : M} {x : V}
    (hx : x ∈ LinearMap.range (c ψ)) (χ : M) :
    c χ x = if ψ = χ then x else 0 := by
  obtain ⟨w, rfl⟩ := hx
  exact hcc ψ χ w

/-- The components of a vector outside a finite set that sums to the vector vanish. -/
theorem graded_apply_eq_zero_of_not_mem
    (hcc : ∀ χ ψ v, c ψ (c χ v) = if χ = ψ then c χ v else 0) {v : V} {s : Finset M}
    (hs : ∑ χ ∈ s, c χ v = v) {ψ : M} (hψ : ψ ∉ s) : c ψ v = 0 := by
  conv_lhs => rw [← hs]
  rw [map_sum]
  simp_rw [hcc]
  rw [Finset.sum_ite_eq']
  simp [hψ]

/-- A subspace stable under the component projections of a grading has a projection
onto it that commutes with the component projections. -/
theorem exists_graded_projection (c : M → V →ₗ[K] V)
    (hcc : ∀ χ ψ v, c ψ (c χ v) = if χ = ψ then c χ v else 0)
    (hfin : ∀ v, ∃ s : Finset M, ∑ χ ∈ s, c χ v = v) (Y : Submodule K V)
    (hY : ∀ χ, ∀ y ∈ Y, c χ y ∈ Y) :
    ∃ π : V →ₗ[K] V, (∀ y ∈ Y, π y = y) ∧ (∀ v, π v ∈ Y) ∧ ∀ χ v, π (c χ v) = c χ (π v) := by
  classical
  -- a projection onto each graded piece of `Y`
  let Yc : M → Submodule K V := fun χ => Y ⊓ LinearMap.range (c χ)
  have hg : ∀ χ, ∃ g : V →ₗ[K] Yc χ, g.comp (Yc χ).subtype = LinearMap.id := fun χ =>
    LinearMap.exists_leftInverse_of_injective (Yc χ).subtype (Yc χ).ker_subtype
  choose g hg using hg
  let q : M → V →ₗ[K] V := fun χ => (Yc χ).subtype ∘ₗ g χ
  have hq_mem : ∀ χ v, q χ v ∈ Yc χ := fun χ v => (g χ v).2
  have hq_fix : ∀ χ, ∀ x ∈ Yc χ, q χ x = x := fun χ x hx => by
    change ((g χ x : Yc χ) : V) = x
    have := DFunLike.congr_fun (hg χ) ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  -- the finitely supported family of components of a vector
  choose s hs using hfin
  have hsupp : ∀ v χ, c χ v ≠ 0 → χ ∈ s v := fun v χ h => by
    by_contra hχ
    exact h (graded_apply_eq_zero_of_not_mem hcc (hs v) hχ)
  let D : V →ₗ[K] (M →₀ V) :=
    { toFun := fun v => Finsupp.onFinset (s v) (fun χ => c χ v) (hsupp v)
      map_add' := fun v w => by
        ext χ
        simp
      map_smul' := fun a v => by
        ext χ
        simp }
  let π : V →ₗ[K] V := Finsupp.lsum K q ∘ₗ D
  -- `π` is the sum of the projected components over any set containing the support
  have hπ : ∀ v (t : Finset M), (∀ χ ∉ t, c χ v = 0) → π v = ∑ χ ∈ t, q χ (c χ v) := by
    intro v t ht
    change (Finsupp.lsum K q) (D v) = _
    rw [Finsupp.lsum_apply, Finsupp.sum_of_support_subset (D v)]
    · rfl
    · intro χ hχ
      by_contra h
      exact (Finsupp.mem_support_iff.mp hχ) (ht χ h)
    · intro χ _
      exact map_zero _
  have hYc : ∀ χ, ∀ y ∈ Y, c χ y ∈ Yc χ := fun χ y hy => ⟨hY χ y hy, ⟨y, rfl⟩⟩
  refine ⟨π, ?_, ?_, ?_⟩
  · intro y hy
    rw [hπ y (s y) fun χ hχ => graded_apply_eq_zero_of_not_mem hcc (hs y) hχ]
    conv_rhs => rw [← hs y]
    exact Finset.sum_congr rfl fun χ _ => hq_fix χ _ (hYc χ y hy)
  · intro v
    rw [hπ v (s v) fun χ hχ => graded_apply_eq_zero_of_not_mem hcc (hs v) hχ]
    exact Y.sum_mem fun χ _ => (hq_mem χ _).1
  · intro χ v
    have hcv : ∀ ψ ∉ ({χ} : Finset M), c ψ (c χ v) = 0 := fun ψ hψ => by
      rw [hcc, ite_eq_right]
      simpa [eq_comm] using hψ
    rw [hπ (c χ v) {χ} hcv, Finset.sum_singleton, hπ v (s v) fun ψ hψ =>
      graded_apply_eq_zero_of_not_mem hcc (hs v) hψ, map_sum]
    have hterm : ∀ ψ, c χ (q ψ (c ψ v)) = if ψ = χ then q ψ (c ψ v) else 0 := fun ψ =>
      graded_apply_of_mem_range hcc (hq_mem ψ _).2 χ
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    split_ifs with hχ
    · rw [hcc, ite_eq_left rfl]
    · rw [hcc, ite_eq_left rfl, graded_apply_eq_zero_of_not_mem hcc (hs v) hχ, map_zero]

end GradedProjection

end Langlands.GroupScheme.TorusLinearization
