import Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclicProof
import Langlands.Cohomology.AnalyticEtaleGlobalComparison.Statement
import Langlands.Cohomology.AnalyticEtaleGlobalComparison.DegreeZero
import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.PointFibersJointlyFaithful
import Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction
import Langlands.Cohomology.CompactSoft.AcyclicityProof
import Langlands.Geometry.Analytic.CommonPointField.Proof
import Langlands.Geometry.Analytic.EtaleGeometricPointProof
import Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalReduction
import Langlands.Sheaf.Equivariant.AnalyticSmoothPointProductCoefficients

/-! # Compact étale global comparison -/

noncomputable section

universe u v uL z

namespace Langlands.Cohomology.AnalyticEtaleGlobalComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic
open AnalyticEtaleRestrictedInjectiveAcyclic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G]
variable (ρ : G →* Aut X)
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Berkovich's compact étale global cohomology comparison. -/
theorem analyticEtaleGlobalComparison :
    AnalyticEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R := by
  intro hX hρ q
  obtain ⟨L, hNorm, hUltra, hComplete, hAlgClosed, hNormAlg, hsurj⟩ :=
    commonAlgebraicallyClosedPointField.{u, v, uL} K X
  let h := EtaleSite.geometricPointStatement K L X
  have hpoints : Function.Surjective (pointProjection L X) := by
    intro x
    obtain ⟨p, hp⟩ := hsurj (ULift.up x)
    exact ⟨p, congrArg ULift.down hp⟩
  have hGodement : AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ := by
    apply analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary L X h R G ρ
    · exact analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced
        L X h R G ρ (analyticEtaleGaloisCoinducedLocalAcyclic L X R G ρ)
    · intro hT2 _ hcont N _ n
      let := hT2
      exact isZero_ordinaryCompactCohomology_coefficientSmoothPointProduct_of_cSoftAcyclicity
        L h ρ R cSoftAcyclicity hcont N n
  have hacyclic := (analyticEtaleRestrictedInjectiveAcyclic_of_godement L X h R G ρ
    (analyticEtalePointFibersJointlyFaithful L X h R) hGodement).2
  let := isIso_etaleGlobalInclusion_of_compactSpace.{u, v, uL, z} ρ R hX
  apply isIso_etaleComparison_of_injective_acyclic.{u, v, uL, z} ρ R _ q
  intro I hI n
  exact hacyclic hX.2 hX.1 hpoints hρ I hI n

end Langlands.Cohomology.AnalyticEtaleGlobalComparison
