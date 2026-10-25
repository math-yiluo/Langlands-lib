import Langlands.Representation.RestrictedTensor.GroupTopology

/-! # Finite coordinates and reference tails in the actual restricted group -/

noncomputable section
open scoped Classical

universe uR uI uG uV

namespace Langlands.RestrictedTensor

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)]
variable (H : ∀ i, Subgroup (G i))

/-- Keep the coordinates in a finite set and replace all others by the identity. -/
def finiteProjection (S : Finset ι) : RestrictedGroup G H →* RestrictedGroup G H where
  toFun g := finiteAssemble H S ((fun i => g i), 1)
  map_one' := by
    ext i
    change (if _ : i ∈ S then (1 : G i) else 1) = 1
    split <;> rfl
  map_mul' g h := by
    ext i
    change (if _ : i ∈ S then g i * h i else 1) =
      (if _ : i ∈ S then g i else 1) * (if _ : i ∈ S then h i else 1)
    by_cases hi : i ∈ S <;> simp [hi]

@[simp]
theorem finiteProjection_apply (S : Finset ι) (g : RestrictedGroup G H) (i : ι) :
    finiteProjection H S g i = if i ∈ S then g i else 1 := by
  change (if _ : i ∈ S then g i else 1) = if i ∈ S then g i else 1
  by_cases hi : i ∈ S <;> simp [hi]

/-- Erase the coordinates in a finite set, preserving the entire remaining tail. -/
def tailProjection (S : Finset ι) : RestrictedGroup G H →* RestrictedGroup G H where
  toFun g := finiteAssemble H S (1, complementProjection H S g)
  map_one' := by
    ext i
    change (if _ : i ∈ S then (1 : G i) else 1) = 1
    split <;> rfl
  map_mul' g h := by
    ext i
    change (if _ : i ∈ S then 1 else g i * h i) =
      (if _ : i ∈ S then 1 else g i) * (if _ : i ∈ S then 1 else h i)
    by_cases hi : i ∈ S <;> simp [hi]

@[simp]
theorem tailProjection_apply (S : Finset ι) (g : RestrictedGroup G H) (i : ι) :
    tailProjection H S g i = if i ∈ S then 1 else g i := by
  change (if _ : i ∈ S then 1 else g i) = if i ∈ S then 1 else g i
  by_cases hi : i ∈ S <;> simp [hi]

theorem finiteProjection_mul_tailProjection (S : Finset ι) (g : RestrictedGroup G H) :
    finiteProjection H S g * tailProjection H S g = g := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

theorem tailProjection_mul_finiteProjection (S : Finset ι) (g : RestrictedGroup G H) :
    tailProjection H S g * finiteProjection H S g = g := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- Finite and complementary coordinates commute even for different elements. -/
theorem finiteProjection_commute_tailProjection (S : Finset ι)
    (g h : RestrictedGroup G H) :
    Commute (finiteProjection H S g) (tailProjection H S h) := by
  change finiteProjection H S g * tailProjection H S h =
    tailProjection H S h * finiteProjection H S g
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

@[simp]
theorem finiteProjection_empty (g : RestrictedGroup G H) :
    finiteProjection H ∅ g = 1 := by
  ext i
  simp

/-- Adding one coordinate multiplies by its genuine singleton insertion. -/
theorem finiteProjection_insert (S : Finset ι) (i : ι) (hi : i ∉ S)
    (g : RestrictedGroup G H) :
    finiteProjection H (insert i S) g =
      RestrictedProduct.mulSingleMonoidHom H i (g i) * finiteProjection H S g := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi, RestrictedProduct.mulSingleMonoidHom]
  · simp [hji, RestrictedProduct.mulSingleMonoidHom]

/-- If all nonreference coordinates are in `S`, the complementary element is
in the full reference tail. -/
theorem tailProjection_mem_tailReferenceSubgroup (S : Finset ι)
    (g : RestrictedGroup G H) (hg : ∀ i ∉ S, g i ∈ H i) :
    tailProjection H S g ∈ tailReferenceSubgroup H S := by
  constructor
  · intro i hi
    simp [hi]
  · intro i hi
    simpa [hi] using hg i hi

/-- Any prescribed finite set can be enlarged to contain the nonreference
coordinates of a restricted-product element. -/
theorem exists_finset_reference_outside (E : Finset ι) (g : RestrictedGroup G H) :
    ∃ S : Finset ι, E ⊆ S ∧ ∀ i ∉ S, g i ∈ H i := by
  obtain ⟨S, hS⟩ := (Filter.eventually_cofinite.mp g.property).exists_finset_coe
  refine ⟨E ∪ S, Finset.subset_union_left, ?_⟩
  intro i hi
  by_contra hg
  have his : i ∈ S := by
    change i ∈ (S : Set ι)
    rw [hS]
    exact hg
  exact hi (Finset.mem_union_right E his)

variable {R : Type uR} [CommRing R] {V : Type uV}
variable [AddCommGroup V] [Module R V]

/-- On a vector fixed by the full reference tail, the action is determined by
the finitely many retained coordinates. -/
theorem apply_eq_finiteProjection_of_tail_fixed
    (π : Representation R (RestrictedGroup G H) V) (S : Finset ι) (v : V)
    (hv : ∀ t ∈ tailReferenceSubgroup H S, π t v = v)
    (g : RestrictedGroup G H) (hg : ∀ i ∉ S, g i ∈ H i) :
    π g v = π (finiteProjection H S g) v := by
  calc
    π g v = π (finiteProjection H S g * tailProjection H S g) v := by
      rw [finiteProjection_mul_tailProjection]
    _ = π (finiteProjection H S g) (π (tailProjection H S g) v) := by
      rw [π.map_mul]
      rfl
    _ = π (finiteProjection H S g) v := by
      rw [hv _ (tailProjection_mem_tailReferenceSubgroup H S g hg)]

end Langlands.RestrictedTensor
