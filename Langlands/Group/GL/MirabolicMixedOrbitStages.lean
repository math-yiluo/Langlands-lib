import Langlands.Group.GL.MirabolicMixedOrbitData

/-! Elementary section and stages calculations for the mixed orbit data. -/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.Geometric
open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

section Retraction

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem levi_projection_first (g : mirabolic n R)
    (i : Fin (n + 1)) (j : Fin n) :
    (levi (projection g)).val.val i j.castSucc = g.val.val i j.castSucc := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [levi_bottom, g.property]
  · rw [levi_first, projection_apply]

theorem rankCast_symm_levi_projection {m : ℕ} (h : m = n) (g : mirabolic n R) :
    (rankCast h).symm (levi (projection g)) =
      levi (projection ((rankCast h).symm g)) := by
  subst h
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem eq_levi_projection_of_lastColumn_eq_zero (g : mirabolic n R)
    (hg : lastColumn g = 0) : g = levi (projection g) := by
  calc
    g = (radicalElement (lastColumn g)).val * levi (projection g) :=
      eq_radicalElement_mul_levi g
    _ = levi (projection g) := by
      rw [hg, radicalElement_zero]
      simp only [Subgroup.coe_one, one_mul]

variable {k r : ℕ}

private theorem leftIndex_first (i : Fin k) :
    leftIndex k r (Sum.inl i) = (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem rightIndex_first (i : Fin r) :
    rightIndex k r (Sum.inl i.castSucc) =
      (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem rightIndex_middle (i : Fin k) :
    rightIndex k r (Sum.inr i) =
      (⟨r + i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

theorem levi_projection_mem_leftSubgroup (g : mirabolic (k + r) R)
    (hg : g ∈ leftSubgroup k r R) :
    levi (projection g) ∈ leftSubgroup k r R := by
  rw [mem_leftSubgroup_iff_entry] at hg ⊢
  intro i j
  rw [leftIndex_first, levi_projection_first]
  simpa only [leftIndex_first] using hg i j

theorem levi_projection_mem_rightSubgroup (g : mirabolic (k + r) R)
    (hg : g ∈ rightSubgroup k r R) :
    levi (projection g) ∈ rightSubgroup k r R := by
  rw [mem_rightSubgroup_iff_entry] at hg ⊢
  intro i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [rightIndex_last, rightIndex_middle, levi_last]
  · rw [rightIndex_first, levi_projection_first]
    simpa only [rightIndex_first] using hg i j.castSucc

end Retraction

section Stages

variable {R : Type u} [CommRing R] {t : ℕ}
  (H : Subgroup (mirabolic (t + 1) R)) (w : mirabolic (t + 1) R)

/-- The actual successor section, restricted to its stabilizer preimage. -/
def sectionInclusion : sectionSubgroup H w →*
    orbitStabilizer H (plusSubgroup t R) w :=
  plusSuccessor.subgroupComap _

@[simp] theorem sectionInclusion_val (g : sectionSubgroup H w) :
    ((sectionInclusion H w g).val : mirabolic (t + 1) R) = successor g.val := rfl

theorem orbitStabilizer_le_stagesSubgroup
    (hH : ∀ g ∈ H, levi (projection g) ∈ H)
    (hw : levi (projection w) = w) :
    orbitStabilizer H (plusSubgroup t R) w ≤ stagesSubgroup H w := by
  intro q hq
  rw [mem_stagesSubgroup_iff]
  change w⁻¹ * levi (projection q.val) * w ∈ H
  have hh := hH _ ((mem_orbitStabilizer_iff H w q).mp hq)
  simpa only [map_mul, map_inv, hw] using hh

variable [TopologicalSpace R]

theorem continuous_sectionInclusion : Continuous (sectionInclusion H w) :=
  (continuous_plusSuccessor.comp continuous_subtype_val).subtype_mk _

end Stages

section ConcreteStages

variable (k r : ℕ) (R : Type u) [CommRing R]

theorem leftRepresentative_levi_projection (i : Fin 2) :
    levi (projection (leftRepresentative k r R i)) = leftRepresentative k r R i := by
  apply Eq.symm
  apply eq_levi_projection_of_lastColumn_eq_zero
  fin_cases i
  · funext j
    change (cycleElement (k + r + 1) k (by omega) R).val.val
      j.castSucc (Fin.last (k + r + 2)) = 0
    rw [cycleElement_last_column]
    simp only [Fin.castSucc_ne_last, ↓reduceIte]
  · exact lastColumn_one

theorem rightRepresentative_levi_projection (i : Fin 2) :
    levi (projection (rightRepresentative k r R i)) = rightRepresentative k r R i := by
  apply Eq.symm
  apply eq_levi_projection_of_lastColumn_eq_zero
  fin_cases i
  · funext j
    change (cycleElement (k + r + 1) r (by omega) R).val.val
      j.castSucc (Fin.last (k + r + 2)) = 0
    rw [cycleElement_last_column]
    simp only [Fin.castSucc_ne_last, ↓reduceIte]
  · exact lastColumn_one

theorem leftStabilizer_le_stages (i : Fin 2) :
    leftStabilizer k r R i ≤ leftStages k r R i := by
  apply orbitStabilizer_le_stagesSubgroup
  · intro g hg
    rw [mem_leftInducing_iff, rankCast_symm_levi_projection]
    exact levi_projection_mem_leftSubgroup _ hg
  · exact leftRepresentative_levi_projection k r R i

theorem rightStabilizer_le_stages (i : Fin 2) :
    rightStabilizer k r R i ≤ rightStages k r R i := by
  apply orbitStabilizer_le_stagesSubgroup
  · intro g hg
    rw [mem_rightInducing_iff, rankCast_symm_levi_projection]
    exact levi_projection_mem_rightSubgroup _ hg
  · exact rightRepresentative_levi_projection k r R i

end ConcreteStages

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
