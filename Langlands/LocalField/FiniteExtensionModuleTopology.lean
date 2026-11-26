import Langlands.LocalField.FiniteExtension
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Spectral and module topology on the original extension field -/

noncomputable section

namespace Langlands.LocalField.FiniteExtension

universe u v

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type v) [Field E] [Algebra F E] [Module.Finite F E]

theorem spectralTopology_eq_moduleTopology :
    (normedField F E).toNormedField.toUniformSpace.toTopologicalSpace =
      moduleTopology F E := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  let := normedField F E
  let := normedAlgebra F E
  let b := Module.finBasis F E
  let : IsModuleTopology F E := IsModuleTopology.iso b.equivFunL.symm
  exact eq_moduleTopology F E

/-- The spectral norm on a finite extension induces the originally supplied module topology. -/
theorem spectralTopology_eq [t : TopologicalSpace E] [IsModuleTopology F E] :
    (normedField F E).toNormedField.toUniformSpace.toTopologicalSpace = t :=
  (spectralTopology_eq_moduleTopology F E).trans (eq_moduleTopology F E).symm

/-- The finite extension, with its supplied module topology, is a nonarchimedean local
field for the spectral valuative relation. No change of underlying field or topology is needed. -/
theorem isLocalField_of_isModuleTopology [t : TopologicalSpace E] [IsModuleTopology F E] :
    letI := valuativeRel F E
    IsNonarchimedeanLocalField E := by
  let := valuativeRel F E
  exact spectralTopology_eq F E ▸ isLocalField F E

end Langlands.LocalField.FiniteExtension
