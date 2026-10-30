import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Group.GL.CompactOpen

/-! # Surjectivity of normalized parabolic and product maps -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification
open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem normalizedParabolicMap_surjective {n : ℕ} (B : BlockShape n)
    (A A' : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier))
    (f : letI := T.topology; A.representation.IntertwiningMap A'.representation)
    (hf : Function.Surjective f) :
    let := T.topology
    Function.Surjective (T.normalizedParabolicInducedMap B f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let χ := B.inflateCharacter (T.leviHalfCharacter B)
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F.Carrier)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F.Carrier
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous A.isSmooth)
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous A'.isSmooth)
  · exact hf

theorem normalizedProductMap_surjective {n : ℕ} (B : BlockShape n)
    (A A' : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (f : letI := T.topology
      ∀ i, (A i).representation.IntertwiningMap (A' i).representation)
    (hf : ∀ i, Function.Surjective (f i)) :
    let := T.topology
    Function.Surjective (T.normalizedProductInducedMap B f) := by
  let := T.topology
  exact normalizedParabolicMap_surjective F T B
    (FiniteTensor.externalSmoothObject A) (FiniteTensor.externalSmoothObject A')
    (FiniteTensor.externalMap f)
    (FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ f hf)

end Langlands.Classification
