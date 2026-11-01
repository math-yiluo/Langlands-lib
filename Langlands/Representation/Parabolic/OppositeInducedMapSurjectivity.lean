import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Group.GL.CompactOpen

/-! # Surjectivity of normalized opposite-parabolic induction maps -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {σ : Representation ℂ (B.Levi F.Carrier) V}
variable {τ : Representation ℂ (B.Levi F.Carrier) W}

/-- Smooth normalized induction from the actual opposite block parabolic
preserves a surjective Levi intertwiner, including across different universes. -/
theorem normalizedOppositeParabolicInducedMap_surjective
    (hσ : letI := T.topology; IsSmooth σ)
    (hτ : letI := T.topology; IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Function.Surjective (T.normalizedOppositeParabolicInducedMap B f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let χ := B.inflateOppositeCharacter (T.oppositeLeviHalfCharacter B)
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F.Carrier)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_oppositeParabolic F.Carrier
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.oppositeLeviProjection F.Carrier)
        (B.oppositeLeviProjectionContinuous F.Carrier).continuous hσ)
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.oppositeLeviProjection F.Carrier)
        (B.oppositeLeviProjectionContinuous F.Carrier).continuous hτ)
  · exact hf

end Langlands.PadicField.TopologicalData
