import Langlands.Sheaf.Equivariant.AnalyticSubgroupInduction
import Langlands.Sheaf.Equivariant.LocalActionFiniteLimits
import Mathlib.CategoryTheory.Adjunction.Restrict

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X) {H : Subgroup G} (hH : IsOpen (H : Set G))
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- Induction of quasi-étale module sheaves from an open subgroup. -/
def quasiEtaleGSheafSubgroupInduction :
    QuasiEtaleGSheaf (ρ.comp H.subtype) (ModuleCat.{max u (v + 1) uL} R) ⥤
      QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  discreteSheafSubgroupInduction hH (fun V => IsCompactSpace V.left)
    (fun _ _ hV => hV) (quasiEtaleTopology X)

/-- The ambient induction-restriction adjunction restricts to quasi-étale
module sheaves. -/
def quasiEtaleGSheafSubgroupInductionAdjunction :
    quasiEtaleGSheafSubgroupInduction.{u, v, uL} ρ hH R ⊣
      quasiEtaleGSheafSubgroupRestriction ρ (ModuleCat.{max u (v + 1) uL} R) hH :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  (subgroupInductionAdjunction ρ H R (quasiEtaleTopology X)).restrictFullyFaithful
    (iC := (compactLiftSystem (ρ.comp H.subtype)).discreteSheafInclusion
      (ModuleCat.{max u (v + 1) uL} R) (twistedQuasiEtaleTopology (ρ.comp H.subtype)))
    (iD := (compactLiftSystem ρ).discreteSheafInclusion
      (ModuleCat.{max u (v + 1) uL} R) (twistedQuasiEtaleTopology ρ))
    (Functor.FullyFaithful.ofFullyFaithful _) (Functor.FullyFaithful.ofFullyFaithful _)
    (Iso.refl _) (Iso.refl _)

/-- Open-subgroup induction preserves finite limits. No refinement hypothesis
on the subgroup is needed. -/
instance quasiEtaleGSheafSubgroupInduction_preservesFiniteLimits :
    PreservesFiniteLimits (quasiEtaleGSheafSubgroupInduction.{u, v, uL} ρ hH R) := by
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := discrete_hasColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  have := discrete_hasExactColimitsOfShape.{max u (v + 1) uL}
    (G := Quotient (QuotientGroup.rightRel H)) R
  let iH := (compactLiftSystem (ρ.comp H.subtype)).discreteSheafInclusion
    (ModuleCat.{max u (v + 1) uL} R) (twistedQuasiEtaleTopology (ρ.comp H.subtype))
  let iG := (compactLiftSystem ρ).discreteSheafInclusion
    (ModuleCat.{max u (v + 1) uL} R) (twistedQuasiEtaleTopology ρ)
  have : PreservesFiniteLimits iH :=
    discreteSheafInclusionFiniteLimits _ _
  have : PreservesFiniteLimits (iH ⋙ subgroupInduction ρ H R (quasiEtaleTopology X)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (quasiEtaleGSheafSubgroupInduction.{u, v, uL} ρ hH R ⋙ iG) :=
    inferInstanceAs (PreservesFiniteLimits
      (iH ⋙ subgroupInduction ρ H R (quasiEtaleTopology X)))
  exact preservesFiniteLimits_of_reflects_of_preserves
    (quasiEtaleGSheafSubgroupInduction.{u, v, uL} ρ hH R) iG

/-- Restriction to an open subgroup preserves injective quasi-étale module
sheaves. Only the full group's finite-refinement hypothesis is used. -/
instance quasiEtaleGSheafSubgroupRestriction_preservesInjectiveObjects :
    (quasiEtaleGSheafSubgroupRestriction ρ
      (ModuleCat.{max u (v + 1) uL} R) hH).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (quasiEtaleGSheafSubgroupInductionAdjunction.{u, v, uL} ρ hH R)

end Langlands.Sheaf.Equivariant.Analytic
