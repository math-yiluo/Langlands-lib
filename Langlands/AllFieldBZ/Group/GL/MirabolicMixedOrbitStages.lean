import Langlands.AllFieldBZ.Group.GL.MirabolicMixedOrbitData
import Langlands.Group.GL.MirabolicMixedOrbitStages

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitStages`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitStages` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.Geometric
open Langlands.GeneralLinear.Mirabolic.MixedProduct hiding leftSection rightSection
universe u

section Retraction
variable {R : Type u} [CommRing R] {n : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.levi_projection_first (g : Langlands.GeneralLinear.mirabolic n R)
    (i : Fin (n + 1)) (j : Fin n) :
    (Langlands.GeneralLinear.Mirabolic.levi (Langlands.GeneralLinear.Mirabolic.projection g)).val.val i j.castSucc = g.val.val i j.castSucc := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Langlands.GeneralLinear.Mirabolic.levi_bottom, g.property]
  · rw [Langlands.GeneralLinear.Mirabolic.levi_first, Langlands.GeneralLinear.Mirabolic.projection_apply]

variable {k r : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.leftIndex_first (i : Fin k) :
    leftIndex k r (Sum.inl i) = (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
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

end Retraction
section Stages
variable {R : Type u} [CommRing R] {t : ℕ}
  (H : Subgroup (Langlands.GeneralLinear.mirabolic (t + 1) R)) (w : Langlands.GeneralLinear.mirabolic (t + 1) R)

variable [TopologicalSpace R]

end Stages
section ConcreteStages
variable (k r : ℕ) (R : Type u) [CommRing R]

end ConcreteStages
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
