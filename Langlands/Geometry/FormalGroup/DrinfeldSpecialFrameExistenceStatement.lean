import Langlands.Geometry.FormalGroup.CompletedUnramifiedResidueMaps
import Langlands.Geometry.FormalGroup.DrinfeldDeligneResidueComparisonStatement
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrame

/-! # Existence of the special formal frame and its matrix algebra -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.FormalGroup.LocalDivision

open IsLocalRing ValuativeRel
open Langlands.LocalGalois.Separable

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- Existence of an actual special formal order module of square height over the
residue field of the completed unramified base, with its rational matrix algebra. -/
def DrinfeldSpecialFrameExistenceStatement (π : 𝒪[K]) : Prop :=
  Irreducible π → IsUnramifiedSubfieldOfReducedDegree K D ι → HasDrinfeldCyclicRelations ι π →
    ∃ Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
        (R := ResidueField (fixedFieldIntegers K)) π,
      Nonempty Φ.val.MatrixCoordinates

end Langlands.FormalGroup.LocalDivision
