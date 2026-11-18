import Langlands.GroupScheme.Reductive.WeilFactorRigidityReduction

/-! # Factor projections of points along a complete orthogonal family of idempotents -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdempotentPoints

variable {R : Type u} [CommRing R] (K : GroupScheme (Spec (CommRingCat.of R))) [IsAffine K.X.left]
variable {C : Type u} [CommRing C] [Algebra R C]

/-- **Killing along a complete orthogonal family.** A homomorphism that kills every component
of every point at the members of a complete orthogonal family of idempotents is trivial. -/
theorem map_eq_one_of_family {N : Type*} [Group N]
    (φ : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C) →* N) {n : ℕ} (e : Fin n → C)
    (he : ∀ i, IsIdempotentElem (e i)) (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (hφ : ∀ i g, φ (proj K (e i) g) = 1)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) : φ g = 1 := by
  classical
  have key : ∀ S : Finset (Fin n), IsIdempotentElem (∑ i ∈ S, e i) ∧
      ∀ g, φ (proj K (∑ i ∈ S, e i) g) = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using IsIdempotentElem.zero, fun g => ?_⟩
      rw [Finset.sum_empty, proj_zero, map_one]
    | insert j S hj ih =>
      obtain ⟨hS, hφS⟩ := ih
      have horthS : e j * ∑ i ∈ S, e i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => horth j i (fun h => hj (h ▸ hi))
      have hidem : IsIdempotentElem (e j + ∑ i ∈ S, e i) := by
        change (e j + ∑ i ∈ S, e i) * (e j + ∑ i ∈ S, e i) = e j + ∑ i ∈ S, e i
        have h2 : (∑ i ∈ S, e i) * e j = 0 := by rw [mul_comm]; exact horthS
        rw [add_mul, mul_add, mul_add, (he j).eq, hS.eq, horthS, h2, add_zero, zero_add]
      rw [Finset.sum_insert hj]
      refine ⟨hidem, fun g => ?_⟩
      rw [← proj_mul_proj_one_sub K (he j) (proj K (e j + ∑ i ∈ S, e i) g), map_mul,
        proj_proj K (he j) hidem, proj_proj K (he j).one_sub hidem]
      have h1 : e j * (e j + ∑ i ∈ S, e i) = e j := by
        rw [mul_add, (he j).eq, horthS, add_zero]
      have h2 : (1 - e j) * (e j + ∑ i ∈ S, e i) = ∑ i ∈ S, e i := by
        rw [sub_mul, one_mul, h1, add_sub_cancel_left]
      rw [h1, h2, hφ, hφS, one_mul]
  have h := (key Finset.univ).2 g
  rwa [hsum, proj_one] at h

end Langlands.GroupScheme.IdempotentPoints
