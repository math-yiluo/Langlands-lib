import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitData
import Langlands.Group.GL.MirabolicMixedOrbitRadicals

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitRadicals`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitRadicals` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.GeneralLinear.Mirabolic.MixedProduct hiding leftSection rightSection
universe u

section Cycle
variable (t a : ℕ) (ha : a ≤ t)

variable (R : Type u) [CommRing R]

end Cycle
section RankCast
variable {R : Type u} [CommRing R] {m n : ℕ}

end RankCast
section MixedRadical
variable {R : Type u} [CommRing R] {k r : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.leftIndex_first (i : Fin k) :
    leftIndex k r (Sum.inl i) = (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.leftIndex_second (i : Fin r) :
    leftIndex k r (Sum.inr i.castSucc) =
      (⟨k + i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightIndex_first (i : Fin r) :
    rightIndex k r (Sum.inl i.castSucc) =
      (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.rightIndex_middle (i : Fin k) :
    rightIndex k r (Sum.inr i) =
      (⟨r + i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

end MixedRadical
section LeftOrbit
variable (k r : ℕ) {R : Type u} [CommRing R]

end LeftOrbit
section RightOrbit
variable (k r : ℕ) {R : Type u} [CommRing R]

end RightOrbit
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
