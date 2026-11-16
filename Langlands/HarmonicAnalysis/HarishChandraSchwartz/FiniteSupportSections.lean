import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Set.Finite.Lattice

/-! # Finite-support families in dependent submodules -/

noncomputable section

universe uR uI uV uJ

namespace Langlands.HarishChandraSchwartz

namespace FiniteSupportSections

variable {R : Type uR} [Semiring R] {ι : Type uI} {V : ι → Type uV}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]

local instance : DecidableEq ι := Classical.decEq ι

/-- The support of a dependent family in its literal component index. -/
def support (f : ∀ i, V i) : Set ι := {i | f i ≠ 0}

@[simp] theorem mem_support (f : ∀ i, V i) (i : ι) :
    i ∈ support f ↔ f i ≠ 0 := Iff.rfl

@[simp] theorem support_zero : support (0 : ∀ i, V i) = ∅ := by
  ext i
  simp [support]

theorem support_add_subset (f g : ∀ i, V i) :
    support (f + g) ⊆ support f ∪ support g := by
  intro i hi
  by_contra h
  simp only [Set.mem_union, mem_support, not_or, not_not] at h
  exact hi (by simp [h.1, h.2])

theorem support_smul_subset (c : R) (f : ∀ i, V i) :
    support (c • f) ⊆ support f := by
  intro i hi h
  exact hi (by simp [h])

/-- Families in the specified component submodules with finite support. -/
def submodule (W : ∀ i, Submodule R (V i)) : Submodule R (∀ i, V i) where
  carrier := {f | (∀ i, f i ∈ W i) ∧ (support f).Finite}
  zero_mem' := ⟨fun i => (W i).zero_mem, by simp⟩
  add_mem' := fun hf hg =>
    ⟨fun i => (W i).add_mem (hf.1 i) (hg.1 i),
      (hf.2.union hg.2).subset (support_add_subset _ _)⟩
  smul_mem' := fun c _ hf =>
    ⟨fun i => (W i).smul_mem c (hf.1 i),
      hf.2.subset (support_smul_subset c _)⟩

@[simp] theorem mem_submodule (W : ∀ i, Submodule R (V i)) (f : ∀ i, V i) :
    f ∈ submodule W ↔ (∀ i, f i ∈ W i) ∧ (support f).Finite := Iff.rfl

/-- Evaluation at a component, with codomain its specified submodule. -/
def component (W : ∀ i, Submodule R (V i)) (i : ι) :
    submodule W →ₗ[R] W i where
  toFun f := ⟨f.val i, f.property.1 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem component_val (W : ∀ i, Submodule R (V i))
    (i : ι) (f : submodule W) : (component W i f).val = f.val i := rfl

/-- Extend one component by zero at every other index. -/
def single (W : ∀ i, Submodule R (V i)) (i : ι) :
    W i →ₗ[R] submodule W := by
  classical
  refine
    { toFun := fun v => ⟨Pi.single i v.val, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · constructor
    · intro j
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
        exact v.property
      · simp [Pi.single_eq_of_ne h]
    · refine (Set.finite_singleton i).subset ?_
      intro j hj
      by_contra h
      exact hj (Pi.single_eq_of_ne h v.val)
  · intro v w
    apply Subtype.ext
    exact (LinearMap.single R V i).map_add v.val w.val
  · intro c v
    apply Subtype.ext
    exact (LinearMap.single R V i).map_smul c v.val

@[simp] theorem single_val (W : ∀ i, Submodule R (V i))
    (i : ι) (v : W i) :
    (single W i v).val = Pi.single i v.val := by
  classical
  rfl

@[simp] theorem component_single_same (W : ∀ i, Submodule R (V i))
    (i : ι) (v : W i) : component W i (single W i v) = v := by
  classical
  apply Subtype.ext
  simp [component]

theorem component_single_ne (W : ∀ i, Submodule R (V i))
    {i j : ι} (h : j ≠ i) (v : W i) :
    component W j (single W i v) = 0 := by
  classical
  apply Subtype.ext
  simp [component, Pi.single_eq_of_ne h]

theorem support_single_subset (W : ∀ i, Submodule R (V i))
    (i : ι) (v : W i) : support (single W i v).val ⊆ {i} := by
  classical
  intro j hj
  by_contra h
  exact hj (by simp [Pi.single_eq_of_ne h])

@[ext] theorem ext (W : ∀ i, Submodule R (V i))
    {f g : submodule W} (h : ∀ i, component W i f = component W i g) :
    f = g := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (h i)

section Restrict

variable {κ : Type uJ} (r : κ → ι)

/-- Restriction of raw families to an index map. -/
def restrict : (∀ i, V i) →ₗ[R] ∀ j, V (r j) where
  toFun f j := f (r j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (f : ∀ i, V i) (j : κ) :
    restrict (R := R) r f j = f (r j) := rfl

theorem support_restrict (f : ∀ i, V i) :
    support (restrict (R := R) r f) = r ⁻¹' support f := rfl

/-- Restriction along an index map with finite fibers preserves finite support.
This permits repeated presentations from a finite set of standard indices. -/
def restrictFiniteFibers (W : ∀ i, Submodule R (V i))
    (hr : ∀ i, (r ⁻¹' {i}).Finite) :
    submodule W →ₗ[R] submodule (fun j => W (r j)) where
  toFun f := ⟨restrict (R := R) r f.val,
    (fun j => f.property.1 (r j)),
    f.property.2.preimage' (fun i _ => hr i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictFiniteFibers_val (W : ∀ i, Submodule R (V i))
    (hr : ∀ i, (r ⁻¹' {i}).Finite) (f : submodule W) (j : κ) :
    (restrictFiniteFibers r W hr f).val j = f.val (r j) := rfl

/-- Restriction preserves finite support when its index map is injective. -/
def restrictSubmodule (W : ∀ i, Submodule R (V i))
    (hr : Function.Injective r) :
    submodule W →ₗ[R] submodule (fun j => W (r j)) where
  toFun f := ⟨restrict (R := R) r f.val,
    (fun j => f.property.1 (r j)),
    Set.Finite.preimage hr.injOn f.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictSubmodule_val (W : ∀ i, Submodule R (V i))
    (hr : Function.Injective r) (f : submodule W) (j : κ) :
    (restrictSubmodule r W hr f).val j = f.val (r j) := rfl

end Restrict

end FiniteSupportSections

end Langlands.HarishChandraSchwartz
