import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Langlands.Algebra.ReducedCharpoly
import Langlands.Group.GL.Basic
import Langlands.Algebra.BinaryReducedNorm
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.SimpleRing.DivisionRing

/-!
# The unit group of a central division algebra over a local field

For a nonarchimedean local field `F` and a finite-dimensional central division
algebra `D` over `F` carrying its `F`-module topology, the topological facts
on `D`, on `Dˣ` and on `GL_n(F)` used by the local Jacquet–Langlands correspondence.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open _root_.Topology

universe u

section GeneralLinear

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)

/-- `GL_n(F)` is Hausdorff. -/
theorem generalLinear_t2Space : T2Space (GeneralLinear n F) := by
  have := Langlands.BruhatTits.localField_t2Space F
  infer_instance

/-- `GL_n(F)` is locally compact. -/
theorem generalLinear_locallyCompactSpace : LocallyCompactSpace (GeneralLinear n F) := by
  have := Langlands.BruhatTits.localField_t2Space F
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  infer_instance

/-- `GL_n(F)` is totally disconnected. -/
theorem generalLinear_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (GeneralLinear n F) := by
  have := Langlands.BruhatTits.localField_totallyDisconnectedSpace F
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → F))
  refine (totallyDisconnectedSpace_iff _).mpr ?_
  exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end GeneralLinear

section Division

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [TopologicalSpace D] [IsModuleTopology F D]

/-- The coordinate isomorphism of a basis is a homeomorphism for the module topology. -/
def coordinateHomeomorph {ι : Type*} [Fintype ι] (b : Module.Basis ι F D) :
    D ≃ₜ (ι → F) :=
  haveI := IsModuleTopology.toContinuousAdd F D
  { toEquiv := b.equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }

include F

/-- Multiplication on `D` is continuous for the module topology. -/
theorem isTopologicalRing : IsTopologicalRing D :=
  IsModuleTopology.isTopologicalRing F D

/-- The module topology on `D` is Hausdorff. -/
theorem t2Space : T2Space D := by
  have := Langlands.BruhatTits.localField_t2Space F
  exact (coordinateHomeomorph F D (Module.finBasis F D)).isEmbedding.t2Space

/-- The module topology on `D` is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace D :=
  (coordinateHomeomorph F D (Module.finBasis F D)).isClosedEmbedding.locallyCompactSpace

/-- The module topology on `D` is totally disconnected. -/
theorem totallyDisconnectedSpace : TotallyDisconnectedSpace D := by
  have := Langlands.BruhatTits.localField_totallyDisconnectedSpace F
  exact (coordinateHomeomorph F D (Module.finBasis F D)).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- `Dˣ`, with Mathlib's unit-group topology, is a topological group. -/
theorem units_isTopologicalGroup : IsTopologicalGroup Dˣ := by
  have := isTopologicalRing F D
  infer_instance

/-- `Dˣ` is Hausdorff. -/
theorem units_t2Space : T2Space Dˣ := by
  have := t2Space F D
  infer_instance

/-- `Dˣ` is locally compact. -/
theorem units_locallyCompactSpace : LocallyCompactSpace Dˣ := by
  have := isTopologicalRing F D
  have := t2Space F D
  have := locallyCompactSpace F D
  infer_instance

/-- `Dˣ` is totally disconnected. -/
theorem units_totallyDisconnectedSpace : TotallyDisconnectedSpace Dˣ := by
  have := totallyDisconnectedSpace F D
  refine (totallyDisconnectedSpace_iff Dˣ).mpr ?_
  exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end Division

end Langlands.JacquetLanglands
