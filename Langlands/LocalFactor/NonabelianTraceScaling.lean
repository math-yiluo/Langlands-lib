import Langlands.LocalFactor.CommonClosure

/-! # Trace pullback and additive-character scaling in the actual common closure -/

noncomputable section

universe uF uL

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {L : PadicField.{uL} p}
  (TF : F.TopologicalData) (TL : L.TopologicalData)
  [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]

/-- Trace pullback commutes with scaling by the same field scalar after inclusion. -/
theorem traceCharacter_scale :
    letI := TF.topology
    letI := TL.topology
    letI := TF.valuativeRel
    letI := TL.valuativeRel
    letI := TF.localField
    letI := TL.localField
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (a : F.Carrierˣ),
      TF.traceCharacter TL (ψ.scale a) =
        (TF.traceCharacter TL ψ).scale (Units.map (algebraMap F.Carrier L.Carrier) a) := by
  let := TF.topology
  let := TL.topology
  let := TF.valuativeRel
  let := TL.valuativeRel
  let := TF.localField
  let := TL.localField
  intro ψ a
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  change ψ ((a : F.Carrier) * Algebra.trace F.Carrier L.Carrier x) =
    ψ (Algebra.trace F.Carrier L.Carrier
      (algebraMap F.Carrier L.Carrier (a : F.Carrier) * x))
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.CommonClosure

open LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual nested inclusion takes a base scalar through the field trace. -/
theorem trace_unitsInclusion_mul (E L : Extension F) (h : E.field ≤ L.field)
    (a : E.fieldˣ) (x : L.field) :
    @Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra
        ((E.unitsInclusion L h a : L.field) * x) =
      (a : E.field) *
        @Algebra.trace E.field L.field _ _ (IntermediateField.inclusion h).toAlgebra x := by
  let : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  change Algebra.trace E.field L.field
      (algebraMap E.field L.field (a : E.field) * x) =
    (a : E.field) * Algebra.trace E.field L.field x
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Scaling the trace character uses exactly the actual nested field inclusion. -/
theorem traceCharacter_scale (E L : Extension F) (h : E.field ≤ L.field) :
    letI := (fieldData F E).topology
    letI := (fieldData F L).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F L).valuativeRel
    letI := (fieldData F E).localField
    letI := (fieldData F L).localField
    ∀ (ψ : AdditiveCharacter F E) (a : E.fieldˣ),
      traceCharacter F E L h (ψ.scale a) =
        (traceCharacter F E L h ψ).scale (E.unitsInclusion L h a) := by
  let := (fieldData F E).topology
  let := (fieldData F L).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F L).valuativeRel
  let := (fieldData F E).localField
  let := (fieldData F L).localField
  intro ψ a
  apply HarmonicAnalysis.UnitaryAdditiveCharacter.ext
  intro x
  simp only [traceCharacter_apply, HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply,
    trace_unitsInclusion_mul]

end Langlands.LocalFactor.CommonClosure
