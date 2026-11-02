import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal

/-! # Minimal closed invariant subsets with finite orbits -/

universe u v

open Set TopologicalSpace

namespace Langlands.AlgebraicGeometry.FiniteOrbitTopology

variable {X : Type u} [TopologicalSpace X]

private lemma mem_closure_finite_iff {S : Set X} (hS : S.Finite) (x : X) :
    x ∈ closure S ↔ ∃ y ∈ S, y ⤳ x := by
  have heq : S = ⋃ y ∈ S, ({y} : Set X) := by simp
  have hclosure : closure S = ⋃ y ∈ S, closure ({y} : Set X) :=
    (congrArg closure heq).trans (hS.closure_biUnion _)
  rw [hclosure]
  simp only [mem_iUnion, specializes_iff_mem_closure, exists_prop]

/-- A nonempty finite subset of a T₀ space contains a point belonging to every
finite subset with the same closure. -/
lemma exists_mem_every_finite_same_closure [T0Space X]
    {S : Set X} (hS : S.Finite) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ T : Set X, T.Finite → closure T = closure S → x ∈ T := by
  obtain ⟨x, hx, hmax⟩ :=
    hS.exists_maximalFor (fun x : X => closure ({x} : Set X)) S hne
  refine ⟨x, hx, ?_⟩
  intro T hT heq
  have hxT : x ∈ closure T := heq.symm ▸ subset_closure hx
  obtain ⟨y, hy, hyx⟩ := (mem_closure_finite_iff hT x).mp hxT
  have hyS : y ∈ closure S := heq ▸ subset_closure hy
  obtain ⟨z, hz, hzy⟩ := (mem_closure_finite_iff hS y).mp hyS
  have hxz : x ⤳ z :=
    specializes_iff_closure_subset.mpr (hmax hz (hzy.trans hyx).closure_subset)
  have hxy : x = y := ((hxz.trans hzy).antisymm hyx).eq
  exact hxy.symm ▸ hy

variable [Setoid X]

/-- A subset is invariant if it is a union of the given equivalence classes. -/
def Invariant (S : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ≈ y → x ∈ S → y ∈ S

omit [TopologicalSpace X] in
lemma invariant_class (x : X) : Invariant {y : X | x ≈ y} := by
  intro y z hyz hxy
  exact Setoid.trans hxy hyz

lemma invariant_closure_of_open_maps
    {R : Type v} [TopologicalSpace R] (s t : R → X)
    (hs : Continuous s) (ht : Continuous t)
    (hso : IsOpenMap s) (hto : IsOpenMap t)
    (hrel : ∀ x y : X, x ≈ y ↔ ∃ r : R, s r = x ∧ t r = y)
    {S : Set X} (hS : Invariant S) : Invariant (closure S) := by
  have heq : s ⁻¹' S = t ⁻¹' S := by
    ext r
    have hr : s r ≈ t r := (hrel _ _).mpr ⟨r, rfl, rfl⟩
    exact ⟨hS hr, hS (Setoid.symm hr)⟩
  have heqc : s ⁻¹' closure S = t ⁻¹' closure S := by
    rw [hso.preimage_closure_eq_closure_preimage hs,
      hto.preimage_closure_eq_closure_preimage ht, heq]
  intro x y hxy hx
  obtain ⟨r, rfl, rfl⟩ := (hrel x y).mp hxy
  change r ∈ s ⁻¹' closure S at hx
  change r ∈ t ⁻¹' closure S
  exact heqc ▸ hx

/-- A minimal nonempty closed invariant subset is a single orbit if closure
preserves invariance and all orbits are finite. -/
lemma eq_class_of_minimal_closed_invariant [T0Space X]
    (hclosure : ∀ S : Set X, Invariant S → Invariant (closure S))
    (hfinite : ∀ x : X, ({y : X | x ≈ y} : Set X).Finite)
    (T : Closeds X)
    (hT : Minimal (fun S : Closeds X => (S : Set X).Nonempty ∧ Invariant (S : Set X)) T)
    {x : X} (hx : x ∈ T) :
    (T : Set X) = {y : X | x ≈ y} := by
  have hcl : ∀ y ∈ T, closure {z : X | y ≈ z} = (T : Set X) := by
    intro y hy
    let S : Closeds X := ⟨closure {z : X | y ≈ z}, isClosed_closure⟩
    have hsub : S ≤ T := by
      apply closure_minimal
      · intro z hz
        exact hT.1.2 hz hy
      · exact T.isClosed
    have hprop : (S : Set X).Nonempty ∧ Invariant (S : Set X) :=
      ⟨⟨y, subset_closure (Setoid.refl y)⟩, hclosure _ (invariant_class y)⟩
    exact congrArg (fun S : Closeds X => (S : Set X))
      (le_antisymm hsub (hT.2 hprop hsub))
  obtain ⟨g, hg, hcommon⟩ :=
    exists_mem_every_finite_same_closure (hfinite x) ⟨x, Setoid.refl x⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hyg : y ≈ g := hcommon _ (hfinite y) ((hcl y hy).trans (hcl x hx).symm)
    exact Setoid.trans hg (Setoid.symm hyg)
  · intro y hxy
    exact hT.1.2 hxy hx

lemma finite_of_minimal_closed_invariant [T0Space X]
    (hclosure : ∀ S : Set X, Invariant S → Invariant (closure S))
    (hfinite : ∀ x : X, ({y : X | x ≈ y} : Set X).Finite)
    (T : Closeds X)
    (hT : Minimal (fun S : Closeds X => (S : Set X).Nonempty ∧ Invariant (S : Set X)) T) :
    (T : Set X).Finite := by
  obtain ⟨x, hx⟩ := hT.1.1
  rw [eq_class_of_minimal_closed_invariant hclosure hfinite T hT hx]
  exact hfinite x

/-- Noetherianity selects a minimal nonempty closed invariant subset inside
any supplied nonempty closed invariant subset. -/
noncomputable def minimalClosedInvariant [NoetherianSpace X]
    (S : Closeds X) (hS : (S : Set X).Nonempty ∧ Invariant (S : Set X)) : Closeds X :=
  Classical.choose (exists_minimal_le_of_wellFoundedLT
    (fun T : Closeds X => (T : Set X).Nonempty ∧ Invariant (T : Set X)) S hS)

lemma minimalClosedInvariant_spec [NoetherianSpace X]
    (S : Closeds X) (hS : (S : Set X).Nonempty ∧ Invariant (S : Set X)) :
    minimalClosedInvariant S hS ≤ S ∧
      Minimal (fun T : Closeds X => (T : Set X).Nonempty ∧ Invariant (T : Set X))
        (minimalClosedInvariant S hS) :=
  Classical.choose_spec (exists_minimal_le_of_wellFoundedLT
    (fun T : Closeds X => (T : Set X).Nonempty ∧ Invariant (T : Set X)) S hS)

lemma minimalClosedInvariant_finite [NoetherianSpace X] [T0Space X]
    (hclosure : ∀ T : Set X, Invariant T → Invariant (closure T))
    (hfinite : ∀ x : X, ({y : X | x ≈ y} : Set X).Finite)
    (S : Closeds X) (hS : (S : Set X).Nonempty ∧ Invariant (S : Set X)) :
    (minimalClosedInvariant S hS : Set X).Finite :=
  finite_of_minimal_closed_invariant hclosure hfinite _ (minimalClosedInvariant_spec S hS).2

end Langlands.AlgebraicGeometry.FiniteOrbitTopology
