import Langlands.Representation.Exponents.GroupedCentralCharacterRetractionProof
import Langlands.Representation.Smooth.CentralOperatorExpansionProof
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof

/-! Finite full-central action on actual opposite Jacquet modules. -/

noncomputable section

namespace Langlands

open FiniteActionSpectrum
open scoped IsMulCommutative

universe uV uF

set_option maxHeartbeats 800000 in
/-- The actual full centre of an opposite Jacquet module has finite operator
span and locally constant action for admissible finite-type ambient input. -/
theorem oppositeJacquetCentralAction
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    IsAdmissible A.ρ →
    Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule →
    let J := CuspidalJacquetMultiplicity.oppositeJacquet T B A
    Module.Finite ℂ
      (Submodule.span ℂ
        (Set.range (fun z : Subgroup.center (B.Levi F.Carrier) => J.ρ (z : _)))) ∧
      IsLocallyConstant
        (fun z : Subgroup.center (B.Levi F.Carrier) => J.ρ (z : _)) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  intro hadm hfg
  let J := CuspidalJacquetMultiplicity.oppositeJacquet T B A
  have hJ : IsAdmissible J.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hadm
  have hJfg := Parabolic.oppositeJacquetFiniteGeneration p F T n B A hadm.1 hfg
  exact ⟨centralActionSpan_finite J.ρ (MonoidHom.id _) hJ hJfg,
    centralAction_isLocallyConstant J.ρ (MonoidHom.id _) continuous_id hJ.1 hJfg⟩

end Langlands
