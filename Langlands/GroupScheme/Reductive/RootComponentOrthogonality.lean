import Langlands.GroupScheme.Reductive.RootComponentCentralizerFactors

/-! # Orthogonality and exclusion of mixed roots between coordinate components -/

noncomputable section

universe u

set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

/-- Every root is detected by at least one of the full integral character
coordinates. -/
theorem exists_root_coordinate_ne_zero (r : M.rootIndex) :
    ∃ i : M.basis.support, D.characters (M.rootDatum.root r) i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz : D.characters (M.rootDatum.root r) = 0 := funext hn
  exact M.rootDatum.ne_zero r (D.characters.injective (hz.trans (map_zero _).symm))

/-- Choose a simple index at which the full character coordinates detect a
specified root. -/
def rootCoordinateWitness (r : M.rootIndex) : M.basis.support :=
  Classical.choose (D.exists_root_coordinate_ne_zero r)

/-- The chosen coordinate is nonzero. -/
theorem rootCoordinateWitness_ne_zero (r : M.rootIndex) :
    D.characters (M.rootDatum.root r) (D.rootCoordinateWitness r) ≠ 0 :=
  Classical.choose_spec (D.exists_root_coordinate_ne_zero r)

/-- A coordinate detecting a root necessarily lies in that root's component. -/
theorem component_eq_of_root_coordinate_ne_zero (r : M.rootIndex) (i : M.basis.support)
    (hi : D.characters (M.rootDatum.root r) i ≠ 0) :
    component M.basis i = D.rootComponent r := by
  by_contra hn
  exact hi (D.root_support r i hn)

/-- The chosen detecting coordinate belongs to the root's Cartan component. -/
theorem rootCoordinateWitness_component (r : M.rootIndex) :
    component M.basis (D.rootCoordinateWitness r) = D.rootComponent r :=
  D.component_eq_of_root_coordinate_ne_zero r _ (D.rootCoordinateWitness_ne_zero r)

/-- A linear combination with two nonzero integral coefficients of roots in
distinct components is nonzero and cannot be a root. -/
theorem mixed_combination_ne_zero_and_not_root
    (r s : M.rootIndex) (hrs : D.rootComponent r ≠ D.rootComponent s)
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a • M.rootDatum.root r + b • M.rootDatum.root s ≠ 0 ∧
      a • M.rootDatum.root r + b • M.rootDatum.root s ∉ Set.range M.rootDatum.root := by
  classical
  let i := D.rootCoordinateWitness r
  let j := D.rootCoordinateWitness s
  have hi := D.rootCoordinateWitness_ne_zero r
  have hj := D.rootCoordinateWitness_ne_zero s
  have hci : component M.basis i = D.rootComponent r := D.rootCoordinateWitness_component r
  have hcj : component M.basis j = D.rootComponent s := D.rootCoordinateWitness_component s
  have hsi : D.characters (M.rootDatum.root s) i = 0 :=
    D.root_support s i (by rw [hci]; exact hrs)
  have hrj : D.characters (M.rootDatum.root r) j = 0 :=
    D.root_support r j (by rw [hcj]; exact Ne.symm hrs)
  let x := a • M.rootDatum.root r + b • M.rootDatum.root s
  have hxi : D.characters x i ≠ 0 := by
    change D.characters (a • M.rootDatum.root r + b • M.rootDatum.root s) i ≠ 0
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsi, mul_zero, add_zero]
    exact mul_ne_zero ha hi
  have hxj : D.characters x j ≠ 0 := by
    change D.characters (a • M.rootDatum.root r + b • M.rootDatum.root s) j ≠ 0
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrj, mul_zero, zero_add]
    exact mul_ne_zero hb hj
  refine ⟨?_, ?_⟩
  · intro hx
    change x = 0 at hx
    exact hxi (by rw [hx, map_zero]; rfl)
  · rintro ⟨t, ht⟩
    have hit : component M.basis i = D.rootComponent t :=
      D.component_eq_of_root_coordinate_ne_zero t i (by rwa [ht])
    have hjt : component M.basis j = D.rootComponent t :=
      D.component_eq_of_root_coordinate_ne_zero t j (by rwa [ht])
    exact hrs (hci.symm.trans (hit.trans (hjt.symm.trans hcj)))

/-- Roots in distinct coordinate components have zero Cartan pairing. -/
theorem pairing_eq_zero_of_rootComponent_ne (r s : M.rootIndex)
    (hrs : D.rootComponent r ≠ D.rootComponent s) : M.rootDatum.pairing r s = 0 := by
  by_contra hn
  have hnot := (D.mixed_combination_ne_zero_and_not_root r s hrs
    1 (-M.rootDatum.pairing r s) one_ne_zero (neg_ne_zero.mpr hn)).2
  apply hnot
  refine ⟨M.rootDatum.reflectionPerm s r, ?_⟩
  rw [M.rootDatum.root_reflectionPerm, M.rootDatum.reflection_apply_root]
  simp only [one_smul, neg_smul, sub_eq_add_neg]

/-- Reflection in a root from another component fixes the given root index. -/
theorem reflectionPerm_eq_of_rootComponent_ne (r s : M.rootIndex)
    (hrs : D.rootComponent r ≠ D.rootComponent s) : M.rootDatum.reflectionPerm s r = r := by
  apply M.rootDatum.root.injective
  rw [M.rootDatum.root_reflectionPerm, M.rootDatum.reflection_apply_root,
    D.pairing_eq_zero_of_rootComponent_ne r s hrs, zero_smul, sub_zero]

end Langlands.GroupScheme.RootComponentCoordinates
