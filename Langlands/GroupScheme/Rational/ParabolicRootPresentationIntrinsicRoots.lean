import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.SubtorusIntertwiningRoots

/-! # Intrinsic positive split-component roots of a specified parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- All positive actual weights of the specified Levi split component, using
this presentation's defining cocharacter. Independence is proved below. -/
def intrinsicPositiveRoots : Set (characterLattice A) :=
  positiveRelativeRoots (a ≫ l ≫ p) r.splitComponentCocharacter

/-- The indecomposable positive weights of the specified Levi split component.
This definition makes no comparison with restricted ambient simple roots. -/
def intrinsicSimpleRoots : Set (characterLattice A) :=
  simpleRelativeRoots (a ≫ l ≫ p) r.splitComponentCocharacter

/-- Every complementary ambient simple root restricts to an actual positive
weight for the defining split-component cocharacter. -/
theorem restrict_mem_intrinsicPositiveRoots
    {α : characterLattice r.data.T}
    (hα : α ∈ simpleRelativeRoots r.data.i r.data.ν) (hαJ : α ∉ r.data.J) :
    r.data.f ≫ α ∈ r.intrinsicPositiveRoots := by
  have hpos : 0 < latticePairing A (r.data.f ≫ α) r.splitComponentCocharacter := by
    rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt]
    exact r.isStandard_splitComponentCocharacter.2.2 α hα hαJ
  have hne : r.data.f ≫ α ≠ 0 := by
    intro hz
    rw [hz, map_zero, LinearMap.zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨?_, hpos⟩
  rw [← r.isCompatible.factor_comp]
  exact (rootRestriction r.data.f r.data.i ⟨α, hα.1.1, hne⟩).property

open RealTorusSpace

/-- The target's restricted simple-root vectors lie in the full real image
of the intrinsic positive split-component roots. -/
theorem restrictedRoots_subset_image_intrinsicPositiveRoots :
    r.restrictedRoots ⊆
      (fun α : characterLattice A => (1 : ℝ) ⊗ₜ[ℤ] α) '' r.intrinsicPositiveRoots := by
  intro x hx
  obtain ⟨α, hα, hαJ, rfl⟩ := r.mem_restrictedRoots.mp hx
  exact ⟨r.data.f ≫ α, r.restrict_mem_intrinsicPositiveRoots hα hαJ, rfl⟩

section Smooth

variable [Smooth G.X.hom]

/-- Two compatible presentations have the same dynamic identity-limit subgroup,
namely the ambient image of a geometric radical of the supplied parabolic. -/
theorem dynamicUnipotent_splitComponentCocharacter_eq
    (s : ParabolicRootPresentation p l a) :
    Dynamic.unipotent (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
        a ≫ l ≫ p) =
      Dynamic.unipotent (CommGroupScheme.groupHom s.splitComponentCocharacter ≫
        a ≫ l ≫ p) := by
  obtain ⟨U, n, hn, _⟩ := r.isCompatible.levi.exists_unipotentRadical
  exact (r.range_comp_radical_eq hn).symm.trans (s.range_comp_radical_eq hn)

/-- The intrinsic positive weights equal the complete nonzero tangent-weight
support of every supplied geometric radical. -/
theorem intrinsicPositiveRoots_eq_subgroupRelativeRoots
    {U : GroupScheme (Spec (CommRingCat.of k))} {n : U ⟶ P}
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    r.intrinsicPositiveRoots =
      RelativeRoot.subgroupRelativeRoots (a ≫ l ≫ p) (SubgroupFunctor.range (n ≫ p)) :=
  (r.subgroupRelativeRoots_radical hn).symm

/-- Complete positive split-component root support is independent of every
root-presentation choice, while retaining the same specified maps. -/
theorem intrinsicPositiveRoots_eq (s : ParabolicRootPresentation p l a) :
    r.intrinsicPositiveRoots = s.intrinsicPositiveRoots := by
  obtain ⟨U, n, hn, _⟩ := r.isCompatible.levi.exists_unipotentRadical
  exact (r.intrinsicPositiveRoots_eq_subgroupRelativeRoots hn).trans
    (s.intrinsicPositiveRoots_eq_subgroupRelativeRoots hn).symm

/-- Indecomposable positive split-component weights are likewise independent.
No root-system realization or ambient-simple-root comparison is assumed. -/
theorem intrinsicSimpleRoots_eq (s : ParabolicRootPresentation p l a) :
    r.intrinsicSimpleRoots = s.intrinsicSimpleRoots := by
  have h := r.intrinsicPositiveRoots_eq s
  change positiveRelativeRoots (a ≫ l ≫ p) r.splitComponentCocharacter =
    positiveRelativeRoots (a ≫ l ≫ p) s.splitComponentCocharacter at h
  simp only [intrinsicSimpleRoots, simpleRelativeRoots, h]

end Smooth

end Langlands.GroupScheme.ParabolicRootPresentation
