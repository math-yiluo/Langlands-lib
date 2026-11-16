import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactCompatibleCovers
import Langlands.Cohomology.SiteCech.FiniteCoverCechSystem
import Langlands.Cohomology.SiteCech.LocalCechExactness

/-! # Actual finite Čech systems on compact objects with action lifts -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech

universe u v z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]
variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} R)]
variable [(quasiEtaleTopology X).WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- The actual Čech complexes of compatible compact covers form a finite test
system when every presheaf nerve term has the supplied finite presentation. -/
def compactCompatibleCechSystem
    (p : ∀ i (c : CompactCompatibleCover ρ i),
      c.cover.CechPresentation (quasiEtaleTopology X) (compactLiftBasisObject ρ)) :
    FiniteCechSystem (fun i =>
      (freeSheafFunctor (quasiEtaleTopology X) R).obj
        (shrinkYoneda.{w}.obj (compactLiftBasisObject ρ i))) where
  Cover := CompactCompatibleCover ρ
  complex _ c := freeCechChainComplex (quasiEtaleTopology X) R
    (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))
  augmentation _ c := (freeCechAugmentation (quasiEtaleTopology X) R
    (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))).f 0
  augmentation_zero _ _ := chainAugmentation_zero _ _
  augmentation_epi _ c := by
    have := c.cover.presheafArrow_isLocallySurjective
      (quasiEtaleTopology X) (compactLiftBasisObject ρ)
    have := quasiIso_freeCechAugmentation_of_locally_surjective
      (quasiEtaleTopology X) R
      (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))
    exact (chainAugmentation_exact_epi _ _).2
  augmentation_exact _ c := by
    have := c.cover.presheafArrow_isLocallySurjective
      (quasiEtaleTopology X) (compactLiftBasisObject ρ)
    have := quasiIso_freeCechAugmentation_of_locally_surjective
      (quasiEtaleTopology X) R
      (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))
    exact (chainAugmentation_exact_epi _ _).1
  positive_exact _ c n := by
    have := c.cover.presheafArrow_isLocallySurjective
      (quasiEtaleTopology X) (compactLiftBasisObject ρ)
    have := quasiIso_freeCechAugmentation_of_locally_surjective
      (quasiEtaleTopology X) R
      (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))
    exact chainAugmentation_positive_exact _
      (freeCechAugmentation (quasiEtaleTopology X) R
        (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))) n
  termSize i c := (p i c).size
  termIndex i c := (p i c).index
  termIso i c n := (p i c).freeTermIso _ _ R n
  local_lift S hS i s := by
    obtain ⟨l⟩ := i.property.2
    obtain ⟨c, t, _, ht⟩ :=
      exists_compactCompatibleCover_cech_lift ρ R S hS i l s
    exact ⟨c, t, ht⟩

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
