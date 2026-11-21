import Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement
import Langlands.Sheaf.Equivariant.AnalyticRepSmoothness

/-!
# Berkovich's ordinary equivariant spectral sequences for compact bases

The spectral-sequence clause of Berkovich's Theorem 1.6.1(ii), on the étale and
quasi-étale analytic sites. Here page 2 uses the canonical `G`-action on the
ordinary cohomology of the restricted sheaf, rather than the cohomology of
smooth sections used in §1.2. The smoothness of that action is a conclusion.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalSpectralSequence

open AnalyticGlobalComposite

universe w u v uL z

/-- Berkovich, Theorem 1.6.1(ii), étale spectral sequence: for compact `X`,
`H^q(X, b^*F)` is smooth for its canonical action. The specified spectral
sequence has second page `H^p(G, H^q(X, b^*F))` and abutment `H^{p+q}(X(G), F)`. -/
def AnalyticEtaleCompactBaseSpectralSequenceStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)),
    letI : HasExt.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
      hasExt_of_hasDerivedCategory _
    let D := DerivedCategory.Plus.ι.obj ((etaleGSheafComplex.{u, v, uL} ρ R).obj F)
    let A := trivialSmoothRep R G
    ∃ hs : ∀ q : ℕ, IsSmooth (etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F),
      (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
        Abelian.Ext.{w} A
          (SmoothRep.of (etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) (hs q)) p)) ∧
      FirstQuadrantAbutmentStatement D A
        (fun n => AddCommGrpCat.of ((etaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F))

/-- Berkovich, Theorem 1.6.1(ii), quasi-étale spectral sequence: for compact `X`,
`H^q(X, b^*F)` is smooth for its canonical action. The specified spectral
sequence has second page `H^p(G, H^q(X, b^*F))` and abutment `H^{p+q}(X(G), F)`. -/
def AnalyticQuasiEtaleCompactBaseSpectralSequenceStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)),
    letI : HasExt.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
      hasExt_of_hasDerivedCategory _
    let D := DerivedCategory.Plus.ι.obj ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F)
    let A := trivialSmoothRep R G
    ∃ hs : ∀ q : ℕ, IsSmooth (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F),
      (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
        Abelian.Ext.{w} A
          (SmoothRep.of (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) (hs q)) p)) ∧
      FirstQuadrantAbutmentStatement D A
        (fun n =>
          AddCommGrpCat.of ((quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F))

end Langlands.Cohomology.AnalyticGlobalSpectralSequence
