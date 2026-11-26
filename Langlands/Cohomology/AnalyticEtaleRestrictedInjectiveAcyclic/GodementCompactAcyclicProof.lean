import Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction
import Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclicProof
import Langlands.Sheaf.Equivariant.AnalyticSmoothPointProductCoefficients
import Langlands.Cohomology.CompactSoft.AcyclicityProof

/-! # Compact acyclicity of restricted analytic equivariant Godement terms

The ordinary compact-acyclicity premise of
`analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary` is discharged by the
c-softness of the ordinary restriction of the actual smooth point product and the proved
c-soft acyclicity theorem `Langlands.Cohomology.cSoftAcyclicity`. The local premise is
supplied by the proved Galois-coinduced local acyclicity theorem through the published
algebraic reduction `analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced`.
-/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Positive ordinary compact cohomology of the ordinary restriction of the actual
restricted smooth point product vanishes, for every coefficient diagram. This is the
ordinary premise of `analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`
in exactly its displayed form; the injectivity and point-surjectivity hypotheses are not
used. -/
theorem ordinaryCompactAcyclic_coefficientRestrictedSmoothPointProduct :
    T2Space (localizedSpaceFunctor.obj X) →
      Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
        ∀ N : Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
          ModuleCat.{max u (v + 1) uL} R,
          Injective N → ∀ q : ℕ,
            IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).obj
              ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
                ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N))) := by
  intro hT2 _ hρ N _ q
  let := hT2
  exact isZero_ordinaryCompactCohomology_coefficientSmoothPointProduct_of_cSoftAcyclicity
    L h ρ R cSoftAcyclicity.{max u (v + 1) uL} hρ N q

/-- The corrected local higher-direct-image statement alone implies Godement compact
acyclicity; the ordinary premise is supplied by
`ordinaryCompactAcyclic_coefficientRestrictedSmoothPointProduct`. -/
theorem analyticEtaleGodementCompactAcyclic_of_correctedLocal
    (hlocal : AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ) :
    AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ :=
  analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary L X h R G ρ hlocal
    (ordinaryCompactAcyclic_coefficientRestrictedSmoothPointProduct L X h R G ρ)

/-- Positive-degree compact-support cohomology of the restriction of every degree-zero
equivariant Godement term vanishes. -/
theorem analyticEtaleGodementCompactAcyclic :
    AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ :=
  analyticEtaleGodementCompactAcyclic_of_correctedLocal L X h R G ρ
    (analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced L X h R G ρ
      (analyticEtaleGaloisCoinducedLocalAcyclic L X R G ρ))

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
