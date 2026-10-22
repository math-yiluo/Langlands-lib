import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite vectors of a representation

These are vectors whose actual orbit spans a finite-dimensional vector space.
No topology, compactness, semisimplicity or finite-dimensional ambient carrier
is required.
-/

noncomputable section

universe uk ug uv uw

namespace Langlands.FiniteVectors

set_option backward.isDefEq.respectTransparency false

variable {k : Type uk} [Field k] {G : Type ug} [Monoid G]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {W : Type uw} [AddCommGroup W] [Module k W]

/-- The linear span of the actual orbit of a vector. -/
def orbitSpan (ρ : Representation k G V) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun g => ρ g v)

theorem action_mem_orbitSpan (ρ : Representation k G V) (g : G) (v : V) :
    ρ g v ∈ orbitSpan ρ v := Submodule.subset_span ⟨g, rfl⟩

theorem self_mem_orbitSpan (ρ : Representation k G V) (v : V) :
    v ∈ orbitSpan ρ v := by
  simpa using action_mem_orbitSpan ρ 1 v

/-- The orbit span is stable under the given monoid action. -/
def orbitSubrepresentation (ρ : Representation k G V) (v : V) :
    Subrepresentation ρ where
  toSubmodule := orbitSpan ρ v
  apply_mem_toSubmodule g w hw := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨h, rfl⟩ := hw
      simpa only [map_mul, Module.End.mul_apply] using action_mem_orbitSpan ρ (g * h) v
    | zero => simp
    | add x y hx hy ihx ihy => simpa using (orbitSpan ρ v).add_mem ihx ihy
    | smul c x hx ih => simpa using (orbitSpan ρ v).smul_mem c ih

/-- The orbit span is the smallest invariant subspace containing the vector. -/
theorem orbitSpan_le (ρ : Representation k G V) (v : V) (S : Subrepresentation ρ)
    (hv : v ∈ S) : orbitSpan ρ v ≤ S.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact S.apply_mem_toSubmodule g hv

/-- Finiteness refers to the orbit span, not to the ambient representation. -/
def IsFiniteVector (ρ : Representation k G V) (v : V) : Prop :=
  Module.Finite k (orbitSpan ρ v)

theorem isFiniteVector_of_mem (ρ : Representation k G V) (S : Subrepresentation ρ)
    [Module.Finite k S.toSubmodule] {v : V} (hv : v ∈ S) : IsFiniteVector ρ v :=
  Submodule.finiteDimensional_of_le (orbitSpan_le ρ v S hv)

theorem isFiniteVector_iff (ρ : Representation k G V) (v : V) :
    IsFiniteVector ρ v ↔
      ∃ S : Subrepresentation ρ, Module.Finite k S.toSubmodule ∧ v ∈ S := by
  constructor
  · intro hv
    exact ⟨orbitSubrepresentation ρ v, hv, self_mem_orbitSpan ρ v⟩
  · rintro ⟨S, hS, hv⟩
    have := hS
    exact isFiniteVector_of_mem ρ S hv

theorem isFiniteVector_zero (ρ : Representation k G V) : IsFiniteVector ρ 0 :=
  by
  have : Module.Finite k (⊥ : Subrepresentation ρ).toSubmodule :=
    (inferInstance : Module.Finite k (⊥ : Submodule k V))
  exact isFiniteVector_of_mem ρ ⊥ (Submodule.zero_mem _)

theorem IsFiniteVector.add {ρ : Representation k G V} {v w : V}
    (hv : IsFiniteVector ρ v) (hw : IsFiniteVector ρ w) :
    IsFiniteVector ρ (v + w) := by
  have : Module.Finite k (orbitSpan ρ v) := hv
  have : Module.Finite k (orbitSpan ρ w) := hw
  have : Module.Finite k
      (orbitSubrepresentation ρ v ⊔ orbitSubrepresentation ρ w).toSubmodule :=
    (inferInstance : Module.Finite k (orbitSpan ρ v ⊔ orbitSpan ρ w : Submodule k V))
  apply isFiniteVector_of_mem ρ (orbitSubrepresentation ρ v ⊔ orbitSubrepresentation ρ w)
  exact Submodule.add_mem_sup (self_mem_orbitSpan ρ v) (self_mem_orbitSpan ρ w)

theorem IsFiniteVector.smul {ρ : Representation k G V} {v : V}
    (hv : IsFiniteVector ρ v) (c : k) : IsFiniteVector ρ (c • v) := by
  have : Module.Finite k (orbitSpan ρ v) := hv
  have : Module.Finite k (orbitSubrepresentation ρ v).toSubmodule := hv
  exact isFiniteVector_of_mem ρ (orbitSubrepresentation ρ v)
    ((orbitSpan ρ v).smul_mem c (self_mem_orbitSpan ρ v))

theorem IsFiniteVector.action {ρ : Representation k G V} {v : V}
    (hv : IsFiniteVector ρ v) (g : G) : IsFiniteVector ρ (ρ g v) := by
  have : Module.Finite k (orbitSpan ρ v) := hv
  have : Module.Finite k (orbitSubrepresentation ρ v).toSubmodule := hv
  exact isFiniteVector_of_mem ρ (orbitSubrepresentation ρ v) (action_mem_orbitSpan ρ g v)

/-- The actual invariant subspace of finite vectors. -/
def subrepresentation (ρ : Representation k G V) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | IsFiniteVector ρ v}
      zero_mem' := isFiniteVector_zero ρ
      add_mem' := fun hv hw => hv.add hw
      smul_mem' := fun c _ hv => hv.smul c }
  apply_mem_toSubmodule g _ hv := hv.action g

@[simp]
theorem mem_subrepresentation (ρ : Representation k G V) (v : V) :
    v ∈ subrepresentation ρ ↔ IsFiniteVector ρ v := Iff.rfl

/-- Right or left actions retain the convention of the supplied representation. -/
def representation (ρ : Representation k G V) :
    Representation k G (subrepresentation ρ).toSubmodule :=
  (subrepresentation ρ).toRepresentation

/-- The faithful equivariant inclusion of finite vectors into the ambient space. -/
def inclusion (ρ : Representation k G V) :
    (representation ρ).IntertwiningMap ρ where
  toLinearMap := (subrepresentation ρ).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem inclusion_injective (ρ : Representation k G V) :
    Function.Injective (inclusion ρ) := Subtype.val_injective

variable {ρ : Representation k G V} {σ : Representation k G W}

/-- An equivariant map takes the orbit span exactly onto the image orbit span. -/
theorem map_orbitSpan (T : ρ.IntertwiningMap σ) (v : V) :
    (orbitSpan ρ v).map T.toLinearMap = orbitSpan σ (T v) := by
  unfold orbitSpan
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span k)
  apply congrArg Set.range
  funext g
  exact Representation.IntertwiningMap.isIntertwining ρ σ T g v

theorem IsFiniteVector.map (T : ρ.IntertwiningMap σ) {v : V}
    (hv : IsFiniteVector ρ v) : IsFiniteVector σ (T v) := by
  have : Module.Finite k (orbitSpan ρ v) := hv
  change Module.Finite k (orbitSpan σ (T v))
  rw [← map_orbitSpan T v]
  infer_instance

theorem isFiniteVector_map_iff (T : ρ.IntertwiningMap σ)
    (hT : Function.Injective T) (v : V) :
    IsFiniteVector σ (T v) ↔ IsFiniteVector ρ v := by
  refine ⟨?_, fun hv => hv.map T⟩
  intro hv
  have : Module.Finite k (orbitSpan σ (T v)) := hv
  let f : orbitSpan ρ v →ₗ[k] orbitSpan σ (T v) :=
    T.toLinearMap.restrict fun x hx => by
      rw [← map_orbitSpan T v]
      exact Submodule.mem_map_of_mem hx
  exact FiniteDimensional.of_injective f (fun x y h =>
    Subtype.ext (hT (congrArg Subtype.val h)))

/-- Restriction of any equivariant map to finite vectors. -/
def map (T : ρ.IntertwiningMap σ) :
    (representation ρ).IntertwiningMap (representation σ) where
  toLinearMap := T.toLinearMap.restrict fun _ hv => hv.map T
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining ρ σ T g v.val

@[simp]
theorem inclusion_map (T : ρ.IntertwiningMap σ)
    (v : (subrepresentation ρ).toSubmodule) :
    inclusion σ (map T v) = T (inclusion ρ v) := rfl

end Langlands.FiniteVectors
