import Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement
import Langlands.Sheaf.Equivariant.AnalyticRepSmoothness

/-!
# The étale compact-support spectral sequence on compact analytic bases

This is the compact-base specialization of the spectral-sequence clause of
Berkovich's Corollary 1.5.2(i), using the Library's point-support model. In
particular it does not assert the sequence on an arbitrary noncompact base.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalSpectralSequence

open AnalyticGlobalComposite

universe w u v uL z

/-- On a compact Hausdorff base covered by the given `L`-valued points, the
canonical action on `H^q_c(X, b^*F)` is smooth. The covariant hyperext sequence
of the derived smooth compact sections has page two given by derived smooth
invariants of this representation and abuts to invariant compact cohomology. -/
def AnalyticEtaleCompactSupportSpectralSequenceOnCompactBaseStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)),
    letI : HasExt.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
      hasExt_of_hasDerivedCategory _
    let D := DerivedCategory.Plus.ι.obj ((etaleGSheafCompactComplex L ρ h R).obj F)
    let A := trivialSmoothRep R G
    ∃ hs : ∀ q : ℕ, IsSmooth (etaleRestrictionCompactCohomologyAction L ρ h R q F),
      (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
        Abelian.Ext.{w} A
          (SmoothRep.of (etaleRestrictionCompactCohomologyAction L ρ h R q F) (hs q)) p)) ∧
      FirstQuadrantAbutmentStatement D A
        (fun n => AddCommGrpCat.of ((etaleGSheafInvariantCompactCohomology L ρ h R n).obj F))

end Langlands.Cohomology.AnalyticGlobalSpectralSequence
