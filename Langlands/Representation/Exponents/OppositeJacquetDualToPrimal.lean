import Langlands.Representation.Exponents.AdmissibleCentralDualToPrimalProof
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Classification.ProductLeviCentralCharacter

/-!
# General-source opposite Jacquet application of local dual-to-primal conversion
-/

noncomputable section

namespace Langlands

universe uF uV

/-- An opposite dual exponent of a general admissible source occurs
as a primal generalized eigencharacter with the same character. -/
theorem oppositeJacquetDualToPrimal
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hχ : T.IsDualJacquetExponent B A χ) :
    IsGeneralizedEigencharacter (T.splitCentreOppositeJacquet B A).ρ χ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  have hadm := Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA
  exact admissibleCentralDualToPrimal
    (B.Levi F.Carrier) (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
    (Fin B.length → F.Carrierˣ)
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A)
    (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
    (B.blockScalarToCenter F.Carrier) hadm χ hχ.2

end Langlands
