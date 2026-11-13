import Langlands.GroupScheme.Reductive.TitsIndex
import Mathlib.Order.Fin.Basic

/-! # Separation of the end weights by the actual Tits positive cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- Evaluate each supplied weight on the actual positive cocharacter of the Tits index. -/
def weightValues {n : ℕ} (χ : Fin (n + 1) → characterLattice d.splitTorus) :
    Fin (n + 1) → ℤ :=
  fun i => latticePairing d.splitTorus (χ i) d.positiveCocharacter

/-- Every simple root has nonnegative value on the actual positive cocharacter. -/
theorem simpleRestriction_pairing_nonneg (a : d.Vertex) :
    0 ≤ latticePairing d.splitTorus (d.rootRestriction a.val) d.positiveCocharacter := by
  by_cases hz : d.rootRestriction a.val = 0
  · simp [hz]
  · exact ((d.compatible a.val hz).mp
      (RootPairing.Base.isPos_of_mem_support a.property)).le

/-- A distinguished simple root has strictly positive value. -/
theorem simpleRestriction_pairing_pos (a : d.Vertex) (ha : a ∈ d.distinguishedVertices) :
    0 < latticePairing d.splitTorus (d.rootRestriction a.val) d.positiveCocharacter := by
  exact (d.compatible a.val ha).mp (RootPairing.Base.isPos_of_mem_support a.property)

variable {n : ℕ} (e : d.Vertex ≃ Fin n)
  (χ : Fin (n + 1) → characterLattice d.splitTorus)
  (hχ : ∀ i : Fin n, d.rootRestriction (e.symm i).val = χ i.castSucc - χ i.succ)

include e hχ

/-- Adjacent weight differences are the values of the numbered simple roots. -/
theorem weightValues_sub (i : Fin n) :
    d.weightValues χ i.castSucc - d.weightValues χ i.succ =
      latticePairing d.splitTorus (d.rootRestriction (e.symm i).val)
        d.positiveCocharacter := by
  rw [hχ i, map_sub, LinearMap.sub_apply]
  rfl

/-- The weight values form a nonincreasing sequence. -/
theorem weightValues_antitone : Antitone (d.weightValues χ) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  have h := d.simpleRestriction_pairing_nonneg (e.symm i)
  rw [← d.weightValues_sub e χ hχ i] at h
  exact sub_nonneg.mp h

/-- A distinguished first vertex makes the first weight strictly larger than all others. -/
theorem first_weightValues_gt (hn : 0 < n)
    (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices)
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    d.weightValues χ i < d.weightValues χ 0 := by
  let j : Fin n := ⟨0, hn⟩
  have hstep := d.simpleRestriction_pairing_pos (e.symm j) hfirst
  rw [← d.weightValues_sub e χ hχ j] at hstep
  have hji : j.succ ≤ i := by
    have hi0 : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext h
    change j.val + 1 ≤ i.val
    dsimp [j]
    omega
  exact lt_of_le_of_lt (d.weightValues_antitone e χ hχ hji) (sub_pos.mp hstep)

/-- A distinguished last vertex makes the last weight strictly smaller than all others. -/
theorem last_weightValues_lt (hn : 0 < n)
    (hlast : e.symm ⟨n - 1, by omega⟩ ∈ d.distinguishedVertices)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    d.weightValues χ (Fin.last n) < d.weightValues χ i := by
  let j : Fin n := ⟨n - 1, by omega⟩
  have hstep := d.simpleRestriction_pairing_pos (e.symm j) hlast
  rw [← d.weightValues_sub e χ hχ j] at hstep
  have hjlast : j.succ = Fin.last n := by
    apply Fin.ext
    change n - 1 + 1 = n
    omega
  have hij : i ≤ j.castSucc := by
    have hi0 : i.val ≠ n := by
      intro h
      apply hi
      exact Fin.ext h
    change i.val ≤ n - 1
    have := i.isLt
    omega
  rw [← hjlast]
  exact lt_of_lt_of_le (sub_pos.mp hstep) (d.weightValues_antitone e χ hχ hij)

/-- The first coordinate character is different from every other character. -/
theorem first_weight_ne (hn : 0 < n)
    (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices)
    (i : Fin (n + 1)) (hi : i ≠ 0) : χ i ≠ χ 0 := by
  intro h
  have hv := d.first_weightValues_gt e χ hχ hn hfirst i hi
  simp only [weightValues, h, lt_self_iff_false] at hv

/-- The last coordinate character is different from every other character. -/
theorem last_weight_ne (hn : 0 < n)
    (hlast : e.symm ⟨n - 1, by omega⟩ ∈ d.distinguishedVertices)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : χ i ≠ χ (Fin.last n) := by
  intro h
  have hv := d.last_weightValues_lt e χ hχ hn hlast i hi
  simp only [weightValues, h, lt_self_iff_false] at hv

end Langlands.GroupScheme.TitsIndexData
