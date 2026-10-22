import Langlands.Representation.Smooth.FixedVectors.Detection
import Langlands.Representation.Smooth.FixedVectors.DetectionStatement

namespace Langlands

universe uR uG uV uW

/-- Fixed-vector generation, detection and dimension descent, with the full
quantifiers and independent universes of the published statement. -/
theorem fixedVectorDetectionDescent :
    FixedVectorDetectionDescentStatement.{uR, uG, uV, uW} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _ G _ V _ _ ρ K _ hK T hT
    exact eq_top_of_fixedVectors_le_of_semisimple ρ K hK T hT
  · intro R _ G _ V _ _ W _ _ ρ σ K hgen f hf
    exact intertwiner_eq_zero_of_fixedVectorsMap_eq_zero K hgen f hf
  · intro R _ G _ _ A K _ f hf
    exact SmoothRep.finrank_fixedVectors_kernel_lt K f hf
  · intro G _ _ _ A K hK _ f hf
    exact SmoothRep.finrank_fixedVectors_image_lt K hK f hf
  · intro G _ _ _ A K hK _ f hf
    exact SmoothRep.finrank_fixedVectors_cokernel_lt K hK f hf
  · intro G _ _ _ A C D K hK _ _ i q hi hq fA fC hcomm hzero
    exact SmoothRep.not_injective_fixedVectorsMap_of_subquotient_witness
      K hK i q hi hq fA fC hcomm hzero

end Langlands
