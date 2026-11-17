import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleCones
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactCechSystem
import Langlands.Cohomology.SiteCech.FiniteCechPresentation

/-! # Čech systems from compact lifted tuple cones -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Cohomology.SiteCech

universe u v z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G]
variable {ρ : G →* Aut X}

namespace CompactCompatibleTupleConesStatement

/-- Actual compact lifted limiting cones supply the all-degree finite
representable presentation required by the compatible-cover Čech system. -/
def cechPresentation [LocallySmall.{w} (QuasiEtaleSite X)]
    (h : CompactCompatibleTupleConesStatement ρ)
    (i : CompactLiftBasis ρ) (c : CompactCompatibleCover ρ i) :
    c.cover.CechPresentation (quasiEtaleTopology X) (compactLiftBasisObject ρ) := by
  classical
  choose t ht hc hl using h i c
  exact c.cover.cechPresentationOfCones
    (quasiEtaleTopology X) (compactLiftBasisObject ρ)
    (fun n α => ⟨(t n α).pt, hc n α, hl n α⟩)
    t (fun n α => Classical.choice (ht n α)) (fun _ _ => Iso.refl _)

variable [IsTopologicalGroup G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]
variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} R)]
variable [(quasiEtaleTopology X).WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- The geometric statement and the authorized refinement hypothesis produce
the actual finite free Čech system used by the acyclicity argument. -/
def finiteCechSystem (h : CompactCompatibleTupleConesStatement ρ) :
    FiniteCechSystem (fun i =>
      (freeSheafFunctor (quasiEtaleTopology X) R).obj
        (shrinkYoneda.{w}.obj (compactLiftBasisObject ρ i))) :=
  compactCompatibleCechSystem ρ R h.cechPresentation

end CompactCompatibleTupleConesStatement

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
