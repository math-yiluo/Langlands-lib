import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.MirabolicMixedProductSubgroups
import Langlands.Group.GL.MirabolicMixedOrbitData

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedOrbitData`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedOrbitData` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
open Langlands.GeneralLinear.Mirabolic.MixedOrbit hiding isTopologicalRing_of_topologicalData
open Langlands.Geometric
open Langlands.GeneralLinear.Mirabolic.MixedProduct hiding leftSection rightSection
universe u

/-! ### Rank transport -/

section RankCast
variable {R : Type u} [CommRing R] {m n : ℕ}

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.reindex_mem_mirabolic (h : m = n) (g : Langlands.GeneralLinear.mirabolic m R) :
    Langlands.GeneralLinear.reindex (R := R) (finCongr (congrArg (· + 1) h)) g.val ∈ Langlands.GeneralLinear.mirabolic n R := by
  subst h
  intro j
  simpa only [Langlands.GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_apply] using g.property j

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedOrbit.reindex_symm_mem_mirabolic (h : m = n) (g : Langlands.GeneralLinear.mirabolic n R) :
    (Langlands.GeneralLinear.reindex (R := R) (finCongr (congrArg (· + 1) h))).symm g.val ∈ Langlands.GeneralLinear.mirabolic m R := by
  subst h
  intro j
  simpa only [Langlands.GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_symm, MulEquiv.refl_apply] using g.property j

variable [TopologicalSpace R]

end RankCast
/-! ### Descending cycles and their permutation matrices -/

section Cycle
variable (t a : ℕ) (ha : a ≤ t)

variable (R : Type u) [CommRing R]

end Cycle
/-! ### Stabilizers in the plus subgroup -/

section Orbit
variable {R : Type u} [CommRing R] {t : ℕ} (H : Subgroup (Langlands.GeneralLinear.mirabolic (t + 1) R))
  (w : Langlands.GeneralLinear.mirabolic (t + 1) R)

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

variable {H}

end Topology
end Orbit
/-! ### Case (II): the left mixed subgroup `P_(K, m)` -/

section Left
variable (k r : ℕ) (R : Type u) [CommRing R]

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

variable [T2Space R]

end Topology
end Left
/-! ### Case (III): the right mixed subgroup `P_(m, K)` -/

section Right
variable (k r : ℕ) (R : Type u) [CommRing R]

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

variable [T2Space R]

end Topology
end Right
/-! ### The supplied p-adic topology -/

section Padic
universe uF

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (k r : ℕ)

/-- The supplied topology on `F.Carrier` is a ring topology. -/
theorem isTopologicalRing_of_topologicalData :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  infer_instance

end Padic
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedOrbit
