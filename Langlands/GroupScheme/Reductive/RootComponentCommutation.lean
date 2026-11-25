import Langlands.GroupScheme.Reductive.RootComponentOrthogonality
import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Rational.RootCommutingPartition

/-! # Actual root groups in different Cartan components commute -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

local instance : CommRing M.ring := M.commRing
local instance : Fintype M.coordinates := M.fintypeCoordinates
local instance : IsAffineHom M.group.X.hom := M.reductive.isAffineHom
local instance : Smooth M.group.X.hom := M.reductive.smooth

variable (k : Type u) [Field k] [Algebra M.ring k]

local instance : IsAffineHom ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
  (M.reductive.isConnectedReductive_algebraMap k).isAffineHom

/-- The actual field-valued coordinate maximal torus of the supplied model. -/
abbrev fieldTorusInclusion (_D : RootComponentCoordinates M) :=
  splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion

/-- The actual field roots belonging to one integral Cartan component. -/
def componentRoots (c : Component M.basis) :
    Set (characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)) :=
  {α | ∃ r : M.rootIndex, D.rootComponent r = c ∧
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
      (M.rootDatum.root r) = α}

/-- Every root in a component set is an actual root of the field group. -/
theorem componentRoots_subset (c : Component M.basis) :
    D.componentRoots k c ⊆ relativeRoots (D.fieldTorusInclusion k) := by
  rintro α ⟨r, _, rfl⟩
  rw [relativeRoots_eq_roots, ← (M.fibrewiseRootDatum.field k).2.1]
  exact ⟨r, CoordinateRootDatum.fieldRealization_root k M.rootDatum r⟩

/-- Every actual field root belongs to its integral Cartan component. -/
theorem exists_mem_componentRoots {α : characterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)}
    (hα : α ∈ relativeRoots (D.fieldTorusInclusion k)) :
    ∃ c : Component M.basis, α ∈ D.componentRoots k c := by
  rw [relativeRoots_eq_roots, ← (M.fibrewiseRootDatum.field k).2.1] at hα
  obtain ⟨r, hr⟩ := hα
  exact ⟨D.rootComponent r, r, rfl,
    (CoordinateRootDatum.fieldRealization_root k M.rootDatum r).symm.trans hr⟩

omit [Algebra M.ring k] in
/-- Every Cartan component contributes a nonempty set of actual roots. -/
theorem componentRoots_nonempty (c : Component M.basis) :
    (D.componentRoots k c).Nonempty := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep c
  refine ⟨_, i, ?_, rfl⟩
  exact (D.simple_component i).trans hi

/-- Strict combinations of actual field roots from distinct coordinate
components are neither zero nor ambient roots. -/
theorem field_no_strict_combinations (r s : M.rootIndex)
    (hrs : D.rootComponent r ≠ D.rootComponent s) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    n • splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root r) +
      m • splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root s) ≠ 0 ∧
    n • splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root r) +
      m • splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root s) ∉ roots (D.fieldTorusInclusion k) := by
  classical
  simp only [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  set f := (splitTorus.characterLatticeEquiv k M.coordinates).symm
  let z := n • M.rootDatum.root r + m • M.rootDatum.root s
  have hns : ∀ (a : ℕ) x, f (a • x) = a • f x := fun a x => f.toAddMonoidHom.map_nsmul a x
  have he : n • f (M.rootDatum.root r) + m • f (M.rootDatum.root s) = f z := by
    simp only [z, AddEquiv.map_add, hns]
  have hmix : z ≠ 0 ∧ z ∉ Set.range M.rootDatum.root := by
    simpa only [z, Nat.cast_smul_eq_nsmul] using
      D.mixed_combination_ne_zero_and_not_root r s hrs (n : ℤ) (m : ℤ)
        (Int.natCast_ne_zero.mpr hn.ne') (Int.natCast_ne_zero.mpr hm.ne')
  have hroots : Set.range (CoordinateRootDatum.fieldRealization k M.rootDatum).root =
      roots (D.fieldTorusInclusion k) := (M.fibrewiseRootDatum.field k).2.1
  constructor
  · intro hz
    rw [he] at hz
    exact hmix.1 (f.injective (hz.trans (AddEquiv.map_zero f).symm))
  · intro hz
    rw [he, ← hroots] at hz
    obtain ⟨t, ht⟩ := hz
    rw [CoordinateRootDatum.fieldRealization_root,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm] at ht
    exact hmix.2 ⟨t, f.injective ht⟩

/-- On every scheme test, root subgroups in different integral components
commute in the actual field fibre of the original group. -/
theorem commute_component_root_groups (r s : M.rootIndex)
    (hrs : D.rootComponent r ≠ D.rootComponent s)
    {Z : Over (Spec (CommRingCat.of k))}
    {x y : Z ⟶ ((baseChange (algebraBaseMap M.ring k)).obj M.group).X}
    (hx : x ∈ (RelativeRoot.subgroup (D.fieldTorusInclusion k)
      (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root r))).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup (D.fieldTorusInclusion k)
      (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root s))).carrier Z) : Commute x y := by
  classical
  let : IsAffineHom ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
    (M.reductive.isConnectedReductive_algebraMap k).isAffineHom
  let : Smooth ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
    (M.reductive.isConnectedReductive_algebraMap k).smooth
  apply RootPairNoncommutation.commute_of_no_strict_combinations
    (G := (baseChange (algebraBaseMap M.ring k)).obj M.group)
    (S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (isSplitTorus_splitTorus M.coordinates) (D.fieldTorusInclusion k)
    _ _ ?_ ?_ (fun n m hn hm => D.field_no_strict_combinations k r s hrs n m hn hm) hx hy
  · rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact fun h => M.rootDatum.ne_zero r
      ((splitTorus.characterLatticeEquiv k M.coordinates).symm.injective
        (h.trans (AddEquiv.map_zero _).symm))
  · rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact fun h => M.rootDatum.ne_zero s
      ((splitTorus.characterLatticeEquiv k M.coordinates).symm.injective
        (h.trans (AddEquiv.map_zero _).symm))

/-- The actual field roots of every component form a commuting root
partition, in the Library's full all-test sense. -/
theorem componentRoots_isCommutingRootPartition (c : Component M.basis) :
    IsCommutingRootPartition (D.fieldTorusInclusion k) (D.componentRoots k c) := by
  rintro α ⟨r, hrc, rfl⟩ β hβ hβc Z x y hx hy
  rw [relativeRoots_eq_roots, ← (M.fibrewiseRootDatum.field k).2.1] at hβ
  obtain ⟨s, hs⟩ := hβ
  rw [CoordinateRootDatum.fieldRealization_root] at hs
  subst β
  have hrs : D.rootComponent r ≠ D.rootComponent s := by
    intro heq
    exact hβc ⟨s, heq.symm.trans hrc, rfl⟩
  exact D.commute_component_root_groups k r s hrs hx hy

end Langlands.GroupScheme.RootComponentCoordinates
