import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The spectral norm of a finite extension of a nonarchimedean local field

For a nonarchimedean local field `F`, normed by `LocalGalois.localNormedField F`, and a finite
field extension `E` of `F` carrying the module topology (`IsModuleTopology F E`), the spectral
norm `spectralNorm F E` is a multiplicative ultrametric norm extending the norm of `F`, and every
`F`-algebra automorphism of `E` is an isometry for it. Its topology is the module topology: both
are the unique Hausdorff vector space topology over the complete field `F`. The normed field
`finiteExtensionNormedField F E` is the spectral normed field whose topology is replaced by the
given topology of `E`, so that the two agree definitionally. See the paired Markdown.
-/

noncomputable section

namespace Langlands.LocalGalois

universe u v

/-- The topology of a finite-dimensional normed space over a complete field is the module
topology. -/
private theorem normed_topology_eq_moduleTopology {K : Type u} {L : Type v}
    [NontriviallyNormedField K] [CompleteSpace K] [NormedField L] [NormedSpace K L]
    [FiniteDimensional K L] :
    (inferInstance : TopologicalSpace L) = moduleTopology K L := by
  have := isModuleTopologyOfFiniteDimensional (𝕜 := K) (E := L)
  exact eq_moduleTopology K L

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (E : Type v) [Field E] [Algebra F E] [FiniteDimensional F E]
variable [TopologicalSpace E] [IsModuleTopology F E]

/-- The topology of the spectral norm of `E / F` is the given (module) topology of `E`. -/
theorem spectralNorm_topology_eq :
    letI := localNormedField F
    letI := localNormedField_ultrametric F
    (spectralNorm.normedField F E).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace E› := by
  have hgiven : ‹TopologicalSpace E› = moduleTopology F E := eq_moduleTopology F E
  let := localNormedField F
  let := localNormedField_ultrametric F
  let := localNormedField_complete F
  rw [hgiven]
  exact @normed_topology_eq_moduleTopology F E _ _ (spectralNorm.normedField F E)
    (spectralNorm.normedSpace F E) _

/-- The spectral normed field structure on a finite extension `E` of the local field `F`, with
its topology replaced by the given topology of `E` (equal by `spectralNorm_topology_eq`). -/
@[instance_reducible]
def finiteExtensionNormedField : NontriviallyNormedField E :=
  letI := localNormedField F
  letI := localNormedField_ultrametric F
  letI := localNormedField_complete F
  { spectralNorm.nontriviallyNormedField F E with
    toMetricSpace := (spectralNorm.metricSpace F E).replaceTopology
      (spectralNorm_topology_eq F E).symm }

/-- The topology of `finiteExtensionNormedField F E` is the given topology of `E`. -/
theorem finiteExtensionNormedField_topology :
    (finiteExtensionNormedField F E).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace E› :=
  rfl

/-- The norm of `finiteExtensionNormedField F E` is the spectral norm. -/
theorem finiteExtensionNormedField_norm (x : E) :
    letI := localNormedField F
    letI := localNormedField_ultrametric F
    (finiteExtensionNormedField F E).norm x = spectralNorm F E x :=
  rfl

/-- The spectral norm is ultrametric. -/
theorem finiteExtensionNormedField_ultrametric :
    letI := finiteExtensionNormedField F E
    IsUltrametricDist E := by
  let := localNormedField F
  let := localNormedField_ultrametric F
  let := finiteExtensionNormedField F E
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    isNonarchimedean_spectralNorm

/-- `E` with the spectral norm is a normed algebra over `F` with the norm of
`localNormedField F`. -/
@[instance_reducible]
def finiteExtensionNormedAlgebra :
    letI := localNormedField F
    letI := finiteExtensionNormedField F E
    NormedAlgebra F E :=
  letI := localNormedField F
  letI := localNormedField_ultrametric F
  letI := localNormedField_complete F
  letI := finiteExtensionNormedField F E
  { (inferInstance : Algebra F E) with
    norm_smul_le r x := by
      rw [Algebra.smul_def, norm_mul]
      exact le_of_eq (congrArg (· * ‖x‖) (spectralNorm_extends r)) }

/-- The spectral norm extends the norm of `F`. -/
theorem finiteExtensionNormedField_norm_algebraMap (x : F) :
    letI := localNormedField F
    letI := finiteExtensionNormedField F E
    ‖algebraMap F E x‖ = ‖x‖ := by
  let := localNormedField F
  let := localNormedField_ultrametric F
  exact spectralNorm_extends x

/-- The spectral norm of a natural number is its norm in `F`. -/
theorem finiteExtensionNormedField_norm_natCast (m : ℕ) :
    letI := localNormedField F
    letI := finiteExtensionNormedField F E
    ‖(m : E)‖ = ‖(m : F)‖ := by
  let := localNormedField F
  let := finiteExtensionNormedField F E
  rw [← map_natCast (algebraMap F E) m]
  exact finiteExtensionNormedField_norm_algebraMap F E (m : F)

/-- Every `F`-algebra automorphism of `E` is an isometry of the spectral norm. -/
theorem finiteExtensionNormedField_norm_algEquiv (σ : E ≃ₐ[F] E) (x : E) :
    letI := finiteExtensionNormedField F E
    ‖σ x‖ = ‖x‖ := by
  let := localNormedField F
  let := localNormedField_ultrametric F
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- `E` is complete for the spectral norm. -/
theorem finiteExtensionNormedField_completeSpace :
    letI := finiteExtensionNormedField F E
    CompleteSpace E := by
  let := localNormedField F
  let := localNormedField_complete F
  let := finiteExtensionNormedField F E
  let := finiteExtensionNormedAlgebra F E
  exact FiniteDimensional.complete F E

/-- Closed balls of the spectral norm are compact. -/
theorem finiteExtensionNormedField_properSpace :
    letI := finiteExtensionNormedField F E
    ProperSpace E := by
  let := localNormedField F
  let := localNormedField_complete F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let := finiteExtensionNormedField F E
  let := finiteExtensionNormedAlgebra F E
  exact FiniteDimensional.proper F E

end Langlands.LocalGalois
