import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Filter.Cofinite

/-! # Compact subgroup and covering assembly from coordinates -/

noncomputable section

universe u v w x y

open scoped Pointwise
open Filter

namespace Langlands.Global.CoordinateCompactAssembly

variable {I : Type u} {A : Type v} [Group A]
  {H : I → Type w} [∀ i, Group (H i)]

/-- The subgroup cut out by membership in the specified local subgroups. -/
def coordinateSubgroup (π : ∀ i, A →* H i) (K : ∀ i, Subgroup (H i)) : Subgroup A where
  carrier := {a | ∀ i, π i a ∈ K i}
  one_mem' i := by simp
  mul_mem' ha hb i := by simpa only [map_mul] using (K i).mul_mem (ha i) (hb i)
  inv_mem' ha i := by simpa only [map_inv] using (K i).inv_mem (ha i)

@[simp] theorem mem_coordinateSubgroup (π : ∀ i, A →* H i)
    (K : ∀ i, Subgroup (H i)) (a : A) :
    a ∈ coordinateSubgroup π K ↔ ∀ i, π i a ∈ K i := Iff.rfl

variable [TopologicalSpace A] [∀ i, TopologicalSpace (H i)]

/-- A continuous lift of the full product of the given local subgroups.
No homomorphism law or compactness assumption is part of this data. -/
structure CompactProductLift (π : ∀ i, A →* H i) (K : ∀ i, Subgroup (H i)) where
  lift : (∀ i, K i) → A
  continuous_lift : Continuous lift
  eval_lift : ∀ (k : ∀ i, K i) (i : I), π i (lift k) = (k i : H i)

variable {π : ∀ i, A →* H i} {K : ∀ i, Subgroup (H i)}

namespace CompactProductLift

variable (D : CompactProductLift π K)

include D

/-- The range is the coordinate subgroup when coordinates distinguish points. -/
theorem range_lift
    (hsep : ∀ a b : A, (∀ i, π i a = π i b) → a = b) :
    Set.range D.lift = (coordinateSubgroup π K : Set A) := by
  ext a
  constructor
  · rintro ⟨k, rfl⟩ i
    rw [D.eval_lift]
    exact (k i).property
  · intro ha
    refine ⟨fun i => ⟨π i a, ha i⟩, ?_⟩
    apply hsep
    intro i
    exact D.eval_lift _ i

/-- Tychonoff compactness transported through the lift. -/
theorem isCompact_coordinateSubgroup
    (hsep : ∀ a b : A, (∀ i, π i a = π i b) → a = b)
    (hK : ∀ i, IsCompact (K i : Set (H i))) :
    IsCompact (coordinateSubgroup π K : Set A) := by
  let : ∀ i, CompactSpace (K i) := fun i => isCompact_iff_compactSpace.mp (hK i)
  rw [← D.range_lift hsep]
  exact isCompact_range D.continuous_lift

/-- Each coordinate image of the global subgroup is the entire local subgroup. -/
theorem map_coordinateSubgroup (i : I) :
    (coordinateSubgroup π K).map (π i) = K i := by
  classical
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact ha i
  · intro a ha
    let k : ∀ j, K j := Pi.mulSingle i (⟨a, ha⟩ : K i)
    refine ⟨D.lift k, ?_, ?_⟩
    · intro j
      rw [D.eval_lift]
      exact (k j).property
    · rw [D.eval_lift]
      simp [k]

end CompactProductLift

/-- Maximality can be tested on continuous coordinate projections if their
images of the coordinate subgroup are all the specified local subgroups. -/
theorem maximal_coordinateSubgroup
    (hπ : ∀ i, Continuous (π i))
    (himage : ∀ i, (coordinateSubgroup π K).map (π i) = K i)
    (hmax : ∀ i, ∀ L : Subgroup (H i), IsCompact (L : Set (H i)) →
      K i ≤ L → L = K i) :
    ∀ L : Subgroup A, IsCompact (L : Set A) → coordinateSubgroup π K ≤ L →
      L = coordinateSubgroup π K := by
  intro L hL hKL
  apply le_antisymm
  · intro a ha i
    have hcompact : IsCompact (L.map (π i) : Set (H i)) := by
      simpa only [Subgroup.coe_map] using hL.image (hπ i)
    have hle : K i ≤ L.map (π i) := by
      rw [← himage i]
      exact Subgroup.map_mono hKL
    have heq := hmax i (L.map (π i)) hcompact hle
    have hm : π i a ∈ L.map (π i) := ⟨a, ha, rfl⟩
    rwa [heq] at hm
  · exact hKL

/-- Compactness and unrestricted maximality of the coordinate subgroup. -/
theorem compact_maximal_coordinateSubgroup
    (D : CompactProductLift π K)
    (hsep : ∀ a b : A, (∀ i, π i a = π i b) → a = b)
    (hπ : ∀ i, Continuous (π i))
    (hK : ∀ i, IsCompact (K i : Set (H i)))
    (hmax : ∀ i, ∀ L : Subgroup (H i), IsCompact (L : Set (H i)) →
      K i ≤ L → L = K i) :
    IsCompact (coordinateSubgroup π K : Set A) ∧
      ∀ L : Subgroup A, IsCompact (L : Set A) → coordinateSubgroup π K ≤ L →
        L = coordinateSubgroup π K :=
  ⟨D.isCompact_coordinateSubgroup hsep hK,
    maximal_coordinateSubgroup hπ D.map_coordinateSubgroup hmax⟩

section Covering

variable {B : Type x} [Group B] {Q : I → Type y} [∀ i, Group (Q i)]
  (f : B →* A) (ρ : ∀ i, B →* Q i) (φ : ∀ i, Q i →* H i)

omit [TopologicalSpace A] [∀ i, TopologicalSpace (H i)] in
/-- Local right-compact decompositions assemble once every ambient element
is in the chosen local subgroup almost everywhere and finite-support families
of source points lift to the actual source group. -/
theorem range_mul_coordinateSubgroup_eq_univ
    (hcompat : ∀ i b, π i (f b) = φ i (ρ i b))
    (hgood : ∀ a : A, ∀ᶠ i in cofinite, π i a ∈ K i)
    (hfiniteLift : ∀ q : ∀ i, Q i, (∀ᶠ i in cofinite, q i = 1) →
      ∃ b : B, ∀ i, ρ i b = q i)
    (hcover : ∀ i, Set.range (φ i) * (K i : Set (H i)) = Set.univ) :
    Set.range f * (coordinateSubgroup π K : Set A) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro a
  have hlocal (i : I) : ∃ q : Q i, (φ i q)⁻¹ * π i a ∈ K i := by
    have hm : π i a ∈ Set.range (φ i) * (K i : Set (H i)) := by
      rw [hcover i]
      exact Set.mem_univ _
    rcases hm with ⟨_, ⟨q, rfl⟩, k, hk, heq⟩
    refine ⟨q, ?_⟩
    rw [← heq, inv_mul_cancel_left]
    exact hk
  let q : ∀ i, Q i := fun i =>
    if π i a ∈ K i then 1 else Classical.choose (hlocal i)
  have hq (i : I) : (φ i (q i))⁻¹ * π i a ∈ K i := by
    by_cases hi : π i a ∈ K i
    · simp [q, hi]
    · simpa [q, hi] using Classical.choose_spec (hlocal i)
  have hqfinite : ∀ᶠ i in cofinite, q i = 1 :=
    (hgood a).mono fun i hi => by simp [q, hi]
  obtain ⟨b, hb⟩ := hfiniteLift q hqfinite
  have hk : (f b)⁻¹ * a ∈ coordinateSubgroup π K := by
    intro i
    rw [map_mul, map_inv, hcompat i b, hb i]
    exact hq i
  exact ⟨f b, ⟨b, rfl⟩, (f b)⁻¹ * a, hk, mul_inv_cancel_left _ _⟩

end Covering

end Langlands.Global.CoordinateCompactAssembly
