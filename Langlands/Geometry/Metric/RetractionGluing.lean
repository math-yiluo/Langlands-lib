import Langlands.Geometry.Metric.KPDefinitions

/-! # Metrics glued from apartments along distance-nonincreasing retractions -/

noncomputable section

namespace Langlands.Geometry.Metric.KP

variable {X : Type*}

/-- Abstract hypotheses of KP Proposition 4.2.3(1) and Proposition 4.2.7 for a
candidate distance `d` on `X` and a family `𝒜` of apartments: any two points
lie in a common apartment; on each apartment `d` is the distance of a
nonpositively curved metric; and every apartment `A` and centre `m ∈ A` admit a
retraction onto `A` which is the identity on `A`, does not increase `d`, and
preserves the distance from `m`. -/
structure IsRetractionGluedDistance (d : X → X → ℝ) (𝒜 : Set (Set X)) : Prop where
  exists_common : ∀ x y : X, ∃ A ∈ 𝒜, x ∈ A ∧ y ∈ A
  apartment : ∀ A ∈ 𝒜, ∃ _ : MetricSpace A,
    (∀ x y : A, dist x y = d x y) ∧ IsNonpositivelyCurved A
  exists_retraction : ∀ A ∈ 𝒜, ∀ m ∈ A, ∃ ρ : X → X, (∀ x, ρ x ∈ A) ∧
    (∀ x ∈ A, ρ x = x) ∧ (∀ x y, d (ρ x) (ρ y) ≤ d x y) ∧ ∀ x, d m (ρ x) = d m x

namespace IsRetractionGluedDistance

variable {d : X → X → ℝ} {𝒜 : Set (Set X)} (h : IsRetractionGluedDistance d 𝒜)
include h

theorem dist_self_of_mem {A : Set X} (hA : A ∈ 𝒜) {x : X} (hx : x ∈ A) : d x x = 0 := by
  obtain ⟨_, hd, -⟩ := h.apartment A hA
  simpa using (hd ⟨x, hx⟩ ⟨x, hx⟩).symm

theorem comm_of_mem {A : Set X} (hA : A ∈ 𝒜) {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    d x y = d y x := by
  obtain ⟨_, hd, -⟩ := h.apartment A hA
  rw [← hd ⟨x, hx⟩ ⟨y, hy⟩, ← hd ⟨y, hy⟩ ⟨x, hx⟩, dist_comm]

theorem nonneg_of_mem {A : Set X} (hA : A ∈ 𝒜) {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    0 ≤ d x y := by
  obtain ⟨_, hd, -⟩ := h.apartment A hA
  rw [← hd ⟨x, hx⟩ ⟨y, hy⟩]
  exact dist_nonneg

theorem eq_of_mem_of_eq_zero {A : Set X} (hA : A ∈ 𝒜) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : d x y = 0) : x = y := by
  obtain ⟨_, hd, -⟩ := h.apartment A hA
  rw [← hd ⟨x, hx⟩ ⟨y, hy⟩] at hxy
  exact congrArg Subtype.val (dist_eq_zero.mp hxy)

theorem triangle_of_mem {A : Set X} (hA : A ∈ 𝒜) {x y z : X} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) : d x z ≤ d x y + d y z := by
  obtain ⟨_, hd, -⟩ := h.apartment A hA
  rw [← hd ⟨x, hx⟩ ⟨z, hz⟩, ← hd ⟨x, hx⟩ ⟨y, hy⟩, ← hd ⟨y, hy⟩ ⟨z, hz⟩]
  exact dist_triangle _ _ _

theorem dist_self (x : X) : d x x = 0 := by
  obtain ⟨A, hA, hx, -⟩ := h.exists_common x x
  exact h.dist_self_of_mem hA hx

theorem comm (x y : X) : d x y = d y x := by
  obtain ⟨A, hA, hx, hy⟩ := h.exists_common x y
  exact h.comm_of_mem hA hx hy

theorem nonneg (x y : X) : 0 ≤ d x y := by
  obtain ⟨A, hA, hx, hy⟩ := h.exists_common x y
  exact h.nonneg_of_mem hA hx hy

theorem eq_of_eq_zero {x y : X} (hxy : d x y = 0) : x = y := by
  obtain ⟨A, hA, hx, hy⟩ := h.exists_common x y
  exact h.eq_of_mem_of_eq_zero hA hx hy hxy

/-- KP Proposition 4.2.3(1): retract a common apartment of `x, y` centred at `x`
and use the triangle inequality inside that apartment. -/
theorem triangle (x y z : X) : d x z ≤ d x y + d y z := by
  obtain ⟨A, hA, hx, hz⟩ := h.exists_common x z
  obtain ⟨ρ, hρA, hρid, hρle, -⟩ := h.exists_retraction A hA x hx
  calc d x z = d (ρ x) (ρ z) := by rw [hρid x hx, hρid z hz]
    _ ≤ d (ρ x) (ρ y) + d (ρ y) (ρ z) := h.triangle_of_mem hA (hρA x) (hρA y) (hρA z)
    _ ≤ d x y + d y z := add_le_add (hρle x y) (hρle y z)

/-- The metric space structure whose distance is `d`. -/
@[reducible] def metricSpace : MetricSpace X where
  dist := d
  dist_self := h.dist_self
  dist_comm := h.comm
  dist_triangle := h.triangle
  eq_of_dist_eq_zero := h.eq_of_eq_zero

theorem dist_metricSpace (x y : X) :
    @dist X h.metricSpace.toDist x y = d x y :=
  rfl

/-- KP Proposition 4.2.7: the parallelogram inequality in a common apartment is
transferred by the retraction centred at the apartment midpoint. -/
theorem isNonpositivelyCurved :
    @IsNonpositivelyCurved X h.metricSpace := by
  let := h.metricSpace
  intro x y
  obtain ⟨A, hA, hx, hy⟩ := h.exists_common x y
  obtain ⟨_, hd, hnpc⟩ := h.apartment A hA
  obtain ⟨m, hm⟩ := hnpc ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨ρ, hρA, hρid, hρle, hρm⟩ := h.exists_retraction A hA m m.2
  refine ⟨m, fun z => ?_⟩
  have hz := hm ⟨ρ z, hρA z⟩
  simp only [hd] at hz
  change 2 * d m z ^ 2 + (1 / 2) * d x y ^ 2 ≤ d x z ^ 2 + d y z ^ 2
  have hxz : d x (ρ z) ≤ d x z := by simpa [hρid x hx] using hρle x z
  have hyz : d y (ρ z) ≤ d y z := by simpa [hρid y hy] using hρle y z
  have hxz0 : 0 ≤ d x (ρ z) := h.nonneg _ _
  have hyz0 : 0 ≤ d y (ρ z) := h.nonneg _ _
  rw [← hρm z]
  nlinarith [mul_le_mul hxz hxz hxz0 (hxz0.trans hxz), mul_le_mul hyz hyz hyz0 (hyz0.trans hyz)]

end IsRetractionGluedDistance

/-- A set carrying the image of an injective distance-preserving map from a
nonpositively curved metric space satisfies the apartment clause of
`IsRetractionGluedDistance`. -/
theorem exists_apartmentMetric_of_injective {P : Type*} [MetricSpace P]
    (hP : IsNonpositivelyCurved P) (d : X → X → ℝ) (e : P → X) (he : Function.Injective e)
    (hd : ∀ a b : P, d (e a) (e b) = dist a b) :
    ∃ _ : MetricSpace (Set.range e),
      (∀ x y : Set.range e, dist x y = d x y) ∧ IsNonpositivelyCurved (Set.range e) := by
  let E : P ≃ Set.range e := Equiv.ofInjective e he
  let : MetricSpace (Set.range e) := MetricSpace.induced E.symm E.symm.injective inferInstance
  have hdist : ∀ x y : Set.range e, dist x y = d x y := by
    intro x y
    change dist (E.symm x) (E.symm y) = d x y
    rw [← hd]
    congr 1
    · exact congrArg Subtype.val (E.apply_symm_apply x)
    · exact congrArg Subtype.val (E.apply_symm_apply y)
  refine ⟨inferInstance, hdist, fun x y => ?_⟩
  obtain ⟨m, hm⟩ := hP (E.symm x) (E.symm y)
  refine ⟨E m, fun z => ?_⟩
  have := hm (E.symm z)
  change 2 * dist (E.symm (E m)) (E.symm z) ^ 2 + (1 / 2) * dist (E.symm x) (E.symm y) ^ 2 ≤
    dist (E.symm x) (E.symm z) ^ 2 + dist (E.symm y) (E.symm z) ^ 2
  rwa [E.symm_apply_apply]

end Langlands.Geometry.Metric.KP
