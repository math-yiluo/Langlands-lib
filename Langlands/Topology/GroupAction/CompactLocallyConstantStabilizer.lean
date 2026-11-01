import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.LocallyConstant.Basic

/-! # Open stabilizers of locally constant functions on compact action spaces -/

noncomputable section

universe u v w t

namespace Langlands.CompactAction

open Topology Filter

variable (G : Type v) [Group G]
  {X : Type u} [MulAction G X] {A : Type w}

/-- Elements fixing the actual function under precomposition by the action. -/
def functionStabilizer (f : X → A) : Subgroup G where
  carrier := {g | ∀ x, f (g • x) = f x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ • x)).symm

@[simp]
theorem mem_functionStabilizer (f : X → A) (g : G) :
    g ∈ functionStabilizer G f ↔ ∀ x, f (g • x) = f x := Iff.rfl

/-- Surjective equivariant pullback preserves the full stabilizer exactly. -/
theorem functionStabilizer_comp_eq {Y : Type*} [MulAction G Y]
    (q : X → Y) (hq : Function.Surjective q)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x) (f : Y → A) :
    functionStabilizer G (f ∘ q) = functionStabilizer G f := by
  apply Subgroup.ext
  intro g
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hq y
    rw [← heq]
    exact h x
  · intro h x
    exact (congrArg f (heq g x)).trans (h (q x))

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [CompactSpace X] [ContinuousSMul G X]

/-- Joint continuity and compactness make local constancy uniform near `1`. -/
theorem functionStabilizer_isOpen (f : LocallyConstant X A) :
    IsOpen (functionStabilizer G f : Set G) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have h : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ (Set.univ : Set X), f (g • x) = f x := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro x _
    have h₁ := (f.isLocallyConstant.comp_continuous continuous_smul).eventually_eq
      ((1 : G), x)
    have h₂ := (f.isLocallyConstant.comp_continuous continuous_snd).eventually_eq
      ((1 : G), x)
    filter_upwards [h₁, h₂] with p hp hpx
    have hp' : f (p.1 • p.2) = f x := by simpa using hp
    exact hp'.trans hpx.symm
  exact h.mono fun g hg x => hg x (Set.mem_univ x)

/-- The open subgroup is constructed from the function, with no fixedness input. -/
def openStabilizer (f : LocallyConstant X A) : OpenSubgroup G :=
  ⟨functionStabilizer G f, functionStabilizer_isOpen G f⟩

@[simp]
theorem mem_openStabilizer (f : LocallyConstant X A) (g : G) :
    g ∈ openStabilizer G f ↔ ∀ x, f (g • x) = f x := Iff.rfl

/-- A finite family has a constructed common open stabilizer, including
the empty family. -/
def finiteOpenStabilizer {ι : Type t} [Finite ι]
    (f : ι → LocallyConstant X A) : OpenSubgroup G :=
  OpenSubgroup.iInfOfFinite (fun i => openStabilizer G (f i))

@[simp]
theorem mem_finiteOpenStabilizer {ι : Type t} [Finite ι]
    (f : ι → LocallyConstant X A) (g : G) :
    g ∈ finiteOpenStabilizer G f ↔ ∀ i x, f i (g • x) = f i x := by
  change (g ∈ (⨅ i, (openStabilizer G (f i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

/-- Intersecting with a prescribed open subgroup gives an explicit refinement. -/
def refinedFiniteOpenStabilizer {ι : Type t} [Finite ι]
    (U : OpenSubgroup G) (f : ι → LocallyConstant X A) : OpenSubgroup G :=
  U ⊓ finiteOpenStabilizer G f

theorem refinedFiniteOpenStabilizer_le {ι : Type t} [Finite ι]
    (U : OpenSubgroup G) (f : ι → LocallyConstant X A) :
    refinedFiniteOpenStabilizer G U f ≤ U := inf_le_left

@[simp]
theorem mem_refinedFiniteOpenStabilizer {ι : Type t} [Finite ι]
    (U : OpenSubgroup G) (f : ι → LocallyConstant X A) (g : G) :
    g ∈ refinedFiniteOpenStabilizer G U f ↔
      g ∈ U ∧ ∀ i x, f i (g • x) = f i x := by
  rw [refinedFiniteOpenStabilizer, OpenSubgroup.mem_inf, mem_finiteOpenStabilizer]

end Langlands.CompactAction
