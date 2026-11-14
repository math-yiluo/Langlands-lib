import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitSections
import Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.GeneralLinear.Mirabolic.MixedProduct hiding leftSection rightSection
universe u

variable (k r : ℕ) (R : Type u) [CommRing R]

section EntryTools
variable {R} {n : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.successor_entry_eq (g : Langlands.GeneralLinear.mirabolic n R)
    (i j : Fin (n + 2)) (a b : Fin (n + 1))
    (hi : i.val = a.val) (hj : j.val = b.val) :
    (Langlands.GeneralLinear.Mirabolic.successor g).val.val i j = g.val.val a b := by
  have hei : i = a.castSucc := Fin.ext hi
  have hej : j = b.castSucc := Fin.ext hj
  rw [hei, hej, Langlands.GeneralLinear.Mirabolic.successor_first]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.successor_last_eq (g : Langlands.GeneralLinear.mirabolic n R)
    (i : Fin (n + 2)) (hi : i.val < n + 1) :
    (Langlands.GeneralLinear.Mirabolic.successor g).val.val i (Fin.last (n + 1)) = 0 := by
  have he : i = (⟨i.val, hi⟩ : Fin (n + 1)).castSucc := Fin.ext rfl
  rw [he, Langlands.GeneralLinear.Mirabolic.successor_last]

end EntryTools
section RightCycle
private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.cycle_inv_conjugate_entry {t a : ℕ} (ha : a ≤ t)
    (g : Langlands.GeneralLinear.mirabolic (t + 1) R) (i j : Fin (t + 2)) :
    ((cycleElement t a ha R)⁻¹ * g * cycleElement t a ha R).val.val i j =
      g.val.val (descendingCycle t a ha i) (descendingCycle t a ha j) := by
  change ((Langlands.GeneralLinear.permutation (t + 2) R (descendingCycle t a ha))⁻¹ * g.val *
    Langlands.GeneralLinear.permutation (t + 2) R (descendingCycle t a ha)).val i j = _
  rw [Langlands.GeneralLinear.mul_permutation_entry, Langlands.GeneralLinear.permutation_inv, Langlands.GeneralLinear.permutation_mul_entry]
  rfl

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightCycle_upper_first (a : Fin (r + 1)) :
    descendingCycle (k + r + 1) r (by omega)
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inl a.castSucc))) =
      (Fin.cast (congrArg (· + 1) (show k + 1 + r = k + r + 1 by omega))
        (rightIndex (k + 1) r (Sum.inl a))).castSucc := by
  refine Fin.lastCases ?_ (fun a => ?_) a
  · apply Fin.ext
    change (if _ = r then _ else if _ then _ else _) = _
    simp only [Fin.val_cast, rightIndex_first_val, Fin.val_last]
    simp
  · apply Fin.ext
    change (if _ = r then _ else if _ then _ else _) = _
    simp only [Fin.val_cast, rightIndex_first_val, Fin.val_castSucc]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightCycle_upper_middle (a : Fin (k + 1)) :
    descendingCycle (k + r + 1) r (by omega)
        (Fin.cast (congrArg (· + 1) (totalRank_eq k r))
          (rightIndex (k + 1) (r + 1) (Sum.inr a))) =
      (Fin.cast (congrArg (· + 1) (show k + 1 + r = k + r + 1 by omega))
        (rightIndex (k + 1) r (Sum.inr a))).castSucc := by
  apply Fin.ext
  change (if _ = r then _ else if _ then _ else _) = _
  simp only [Fin.val_cast, rightIndex_middle_val, Fin.val_castSucc]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

end RightCycle
section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
