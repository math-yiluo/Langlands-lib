import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual spectral local-field structure on a finite field extension. -/

noncomputable section

namespace Langlands.LocalField.FiniteExtension

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

local instance baseNormedField : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance baseComplete : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance baseUltrametric : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

/-- The multiplicative spectral norm on the original finite extension field. -/
@[instance_reducible]
def normedField : NontriviallyNormedField L :=
  spectralNorm.nontriviallyNormedField K L

/-- The original scalar action is normed for the chosen extension norm. -/
@[instance_reducible]
def normedAlgebra :
    letI := normedField K L
    NormedAlgebra K L :=
  spectralNorm.normedAlgebra K L

/-- The spectral extension norm is nonarchimedean. -/
theorem ultrametric :
    letI := normedField K L
    IsUltrametricDist L := by
  let := normedField K L
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  exact isNonarchimedean_spectralNorm

/-- The valuative relation of the actual spectral extension valuation. -/
@[instance_reducible]
def valuativeRel : ValuativeRel L :=
  ValuativeRel.ofValuation (LocalGalois.spectralValuation K L)

/-- Norm comparisons recover the actual spectral valuation comparisons. -/
theorem norm_le_iff (x y : L) :
    letI := normedField K L
    ‖x‖ ≤ ‖y‖ ↔ LocalGalois.spectralValuation K L x ≤
      LocalGalois.spectralValuation K L y := Iff.rfl

/-- The extension's valuative relation restricts to the original relation on the base. -/
theorem algebraMap_vle_iff (x y : K) :
    letI := valuativeRel K L
    ValuativeRel.vle (algebraMap K L x) (algebraMap K L y) ↔ ValuativeRel.vle x y := by
  let := valuativeRel K L
  change spectralNorm K L (algebraMap K L x) ≤
      spectralNorm K L (algebraMap K L y) ↔ ValuativeRel.vle x y
  rw [spectralNorm_extends, spectralNorm_extends, LocalGalois.localNormedField_le]
  exact (Valuation.Compatible.vle_iff_le x y).symm

/-- Every finite extension is a nonarchimedean local field for its spectral structures. -/
theorem isLocalField :
    letI := normedField K L
    letI := valuativeRel K L
    IsNonarchimedeanLocalField L := by
  let := normedField K L
  let := normedAlgebra K L
  let := ultrametric K L
  let := valuativeRel K L
  let : (LocalGalois.spectralValuation K L).Compatible :=
    Valuation.Compatible.ofValuation _
  let : (NormedField.valuation (K := L)).Compatible :=
    ⟨fun _ _ => Iff.rfl⟩
  let := NormedField.toValued (K := L)
  let : IsValuativeTopology L :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => Valued.mem_nhds_zero)
  let : ProperSpace L := FiniteDimensional.proper K L
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))).mpr
      inferInstance
  exact {}

end Langlands.LocalField.FiniteExtension
