import Langlands.Representation.Parabolic.InductionExactnessProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Induction.Equivalences
import Langlands.AllField.Representation.Parabolic.ExactnessReciprocityStatement
import Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement
noncomputable section

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uG uU uV uW


end Langlands.AllField.Induction

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding InductionExactnessClause NormalizedInductionExactnessClause inductionExactness normalizedInductionExactness
open Langlands.AllField.Parabolic

universe uF uU uV uW

/-- Actual unnormalized block-parabolic smooth induction preserves short exact sequences. -/
theorem inductionExactness
    (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    InductionExactnessClause F T B U V W := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro ρ σ τ i q _hρ hσ hτ hi hq hex
  dsimp only
  refine ⟨Induction.smoothInducedMap_injective _ _ hi,
    Induction.smoothInducedMap_range_eq_ker _ _ _ hi hex, ?_⟩
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F
  · exact isSmooth_comp (B.leviProjection F)
      (B.leviProjectionContinuous F).continuous hσ
  · exact isSmooth_comp (B.leviProjection F)
      (B.leviProjectionContinuous F).continuous hτ
  · exact hq

/-- Actual positive-half-modulus normalized induction preserves short exact sequences. -/
theorem normalizedInductionExactness
    (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    NormalizedInductionExactnessClause F T B U V W := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  intro ρ σ τ i q hρ hσ hτ hi hq hex
  let χ := T.leviHalfCharacter B
  exact inductionExactness F T B U V W
    (twist χ.toMonoidHom ρ) (twist χ.toMonoidHom σ) (twist χ.toMonoidHom τ)
    (twistIntertwining χ.toMonoidHom i) (twistIntertwining χ.toMonoidHom q)
    ((isSmooth_twist_iff χ.toMonoidHom ρ χ.isOpen_ker).mpr hρ)
    ((isSmooth_twist_iff χ.toMonoidHom σ χ.isOpen_ker).mpr hσ)
    ((isSmooth_twist_iff χ.toMonoidHom τ χ.isOpen_ker).mpr hτ) hi hq hex

end Langlands.AllField.Parabolic
