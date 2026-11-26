import Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction
import Langlands.TraceFormula.GeneralLinearWeilTwistedCompactQuotientProof

/-! # The twisted elliptic centralizer theorem for the Weil restriction of `GL_n` -/

noncomputable section

open NumberField MeasureTheory Topology CategoryTheory AlgebraicGeometry
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.QuotientIntegration
open Langlands.GroupScheme Langlands.TraceFormula.AdelicGroupAutomorphism
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.TraceFormula

-- Keep the adelic group and its subgroup constructions opaque during elaboration.
attribute [local irreducible] Global.AdelicGroupPoints.normOneSubgroup
  Global.AdelicGroupPoints.rationalNormOneSubgroup
  AdelicGroupAutomorphism.normOneAut AdelicGroupAutomorphism.unitGaloisAut twistedCentralizer
  GroupScheme.AffineWeil.corepresentableBy GroupScheme.AffineWeil.tensorFunctor
  Global.AdelicGroupPoints.topologicalSpace

attribute [local instance] generalLinearTwistedEllipticCentralizerIsAffine
  generalLinearTwistedEllipticCentralizerSmooth

set_option hygiene false in
local notation "Wₙ" => weilGroup K L (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K))

private def subgroupOfPoint {H : Type*} [Group H] {Λ : Subgroup H} (_ : Λ) : Subgroup H := Λ

set_option maxRecDepth 2000 in
set_option maxHeartbeats 600000 in
/-- A rational class with regular elliptic norm at a finite place has finite twisted
centralizer quotient volume and integrable twisted orbit functions. -/
theorem generalLinearTwistedEllipticCentralizer : GeneralLinearTwistedEllipticCentralizerStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n θ Φ norm w r hw
  let hcoords : GeneralLinearWeilAdelicTwistStatement.{u} := generalLinearWeilAdelicTwist
  obtain ⟨δ, hr, hδ⟩ :=
    exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm
      (K := K) (L := L) (σ := σ) (n := n) (l := l) hcoords hcyc r w hw
  let H := (fun {G : Type u} (_ : G) => G) r.val
  let C := twistedCentralizer θ r.val
  let Γ := (subgroupOfPoint r).subgroupOf C
  have hc : CompactSpace (LeftQuotient Γ) :=
    generalLinearWeilTwistedCompactQuotient K L σ l hcyc n r δ hr hδ
  have ho : IsClosed (TwistedOrbit θ (r.val : H)) :=
    generalLinearWeilTwistedClosedOrbit K L σ l hcyc n r δ hr hδ
  constructor
  · intro _ _ μC _ _ _ ν hν
    have hfinite := hν.regular.toIsFiniteMeasureOnCompacts
    have hmass : ν Set.univ < ⊤ := by
      apply hfinite.lt_top_of_isCompact
      change IsCompact (Set.univ : Set (LeftQuotient Γ))
      exact hc.isCompact_univ
    exact hmass.ne
  · intro mQ bQ μC _ _ _ ν hν f hf hfs
    let : SecondCountableTopology H := AdelicGroupPoints.normOneSecondCountableTopology K Wₙ
    let : LocallyCompactSpace H := AdelicGroupPoints.normOneLocallyCompactSpace K Wₙ
    let : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
    exact @twistedOrbitFunction_integrable_of_isClosed H inferInstance inferInstance θ r.val
      inferInstance inferInstance inferInstance inferInstance ho mQ bQ ν
      hν.regular.toIsFiniteMeasureOnCompacts f hf hfs

end Langlands.TraceFormula
