import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Support

/-!
# Sums over the left cosets of an open subgroup

For a subgroup `U` of a group `G` and a function `f : G → M`, `cosetSum U f` is the
finitary sum `∑ᶠ q : G ⧸ U, f q.out` over the left cosets `g U`, evaluated at Mathlib's
chosen representatives. For right `U`-invariant functions the representatives do not
matter, and the sum is invariant under left translation of the argument. When `U` is
open and `f` vanishes off a compact set, only finitely many cosets contribute.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Function

universe uG uM uα uβ

variable {G : Type uG} [Group G]

section Algebra

variable {M : Type uM} [AddCommMonoid M]

/-- The sum of `f` over the left cosets of `U`, at Mathlib's chosen representatives. -/
def cosetSum (U : Subgroup G) (f : G → M) : M :=
  ∑ᶠ q : G ⧸ U, f q.out

/-- Invariance of a function under right translation by the elements of `U`. -/
def RightInvariant (U : Subgroup G) (f : G → M) : Prop :=
  ∀ g : G, ∀ u ∈ U, f (g * u) = f g

omit [AddCommMonoid M] in
theorem RightInvariant.apply_out {U : Subgroup G} {f : G → M} (hf : RightInvariant U f)
    (g : G) : f (QuotientGroup.mk g : G ⧸ U).out = f g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu]
  exact hf g u u.2

/-- A right `U`-invariant coset sum is invariant under left translation. -/
theorem cosetSum_mul_left {U : Subgroup G} {f : G → M} (hf : RightInvariant U f) (a : G) :
    cosetSum U (fun g => f (a * g)) = cosetSum U f := by
  unfold cosetSum
  have h : ∀ q : G ⧸ U, f (a * q.out) = f (a • q).out := by
    intro q
    rw [← MulAction.Quotient.mk_smul_out, hf.apply_out]
    rfl
  simp_rw [h]
  exact finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ U)) (f := fun q => f q.out)

theorem cosetSum_congr {U : Subgroup G} {f f' : G → M} (h : ∀ g, f g = f' g) :
    cosetSum U f = cosetSum U f' := by
  unfold cosetSum
  simp_rw [h]

theorem cosetSum_eq_zero {U : Subgroup G} {f : G → M} (h : ∀ g, f g = 0) :
    cosetSum U f = 0 := by
  unfold cosetSum
  simp [h]

end Algebra

/-- Two finitary sums with finitely supported summands commute. -/
theorem finsum_comm_of_finite {α : Type uα} {β : Type uβ} {M : Type uM} [AddCommMonoid M]
    (F : α → β → M) {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite)
    (hF : ∀ a b, F a b ≠ 0 → a ∈ s ∧ b ∈ t) :
    ∑ᶠ a, ∑ᶠ b, F a b = ∑ᶠ b, ∑ᶠ a, F a b := by
  classical
  have h1 : ∀ a, ∑ᶠ b, F a b = ∑ b ∈ ht.toFinset, F a b := fun a =>
    finsum_eq_sum_of_support_subset _ (by
      intro b hb
      simpa using (hF a b hb).2)
  have h2 : ∀ b, ∑ᶠ a, F a b = ∑ a ∈ hs.toFinset, F a b := fun b =>
    finsum_eq_sum_of_support_subset _ (by
      intro a ha
      simpa using (hF a b ha).1)
  simp_rw [h1, h2]
  rw [finsum_eq_sum_of_support_subset (s := hs.toFinset),
    finsum_eq_sum_of_support_subset (s := ht.toFinset), Finset.sum_comm]
  · intro b hb
    obtain ⟨a, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    simpa using (hF a b ha.2).2
  · intro a ha
    obtain ⟨b, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    simpa using (hF a b hb.2).1

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of a compact set in the discrete quotient by an open subgroup is finite. -/
theorem finite_image_mk {U : Subgroup G} (hU : IsOpen (U : Set G)) {K : Set G}
    (hK : IsCompact K) : (QuotientGroup.mk '' K : Set (G ⧸ U)).Finite := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  exact (hK.image QuotientGroup.continuous_mk).finite_of_discrete

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_image_mk_of_out_mem {U : Subgroup G} {K : Set G} {q : G ⧸ U} (hq : q.out ∈ K) :
    q ∈ (QuotientGroup.mk '' K : Set (G ⧸ U)) :=
  ⟨q.out, hq, QuotientGroup.out_eq' q⟩

/-- A function vanishing off a compact set contributes to finitely many cosets of an open
subgroup. -/
theorem hasFiniteSupport_out {M : Type uM} [Zero M] {U : Subgroup G} (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {φ : G → M} (hφ : ∀ g, φ g ≠ 0 → g ∈ K) :
    (fun q : G ⧸ U => φ q.out).HasFiniteSupport :=
  (finite_image_mk hU hK).subset fun _ hq => mem_image_mk_of_out_mem (hφ _ hq)

theorem hasFiniteSupport_out_of_hasCompactSupport {M : Type uM} [Zero M] {U : Subgroup G}
    (hU : IsOpen (U : Set G)) {φ : G → M} (hφ : HasCompactSupport φ) :
    (fun q : G ⧸ U => φ q.out).HasFiniteSupport :=
  hasFiniteSupport_out hU hφ fun _ hg => subset_tsupport φ hg

end Topology

end Langlands.Cohomology.SupercuspidalExtCharZero
