import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactLiftBasis
import Langlands.Cohomology.SiteCech.FiniteCoverCechLifting

/-! # Cofinal compact covers with compatible local actions -/

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
variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- A finite cover by compact objects carrying actual source and target lifts
whose actions commute with every covering arrow on one open subgroup. -/
structure CompactCompatibleCover (i : CompactLiftBasis ρ) where
  cover : FiniteBasisCover (quasiEtaleTopology X)
    (compactLiftBasisObject ρ) (compactLiftBasisObject ρ i)
  targetLift : ActionLift ρ (compactLiftBasisObject ρ i).hom
  sourceLift : ∀ j, ActionLift ρ (compactLiftBasisObject ρ (cover.index j)).hom
  subgroup : OpenSubgroup G
  le_target : (subgroup : Subgroup G) ≤ targetLift.subgroup
  le_source : ∀ j, (subgroup : Subgroup G) ≤ (sourceLift j).subgroup
  equivariant : ∀ j (g : G) (hg : g ∈ subgroup),
    (liftAction (U := (ι quasiEtale ρ).obj (compactLiftBasisObject ρ (cover.index j)))
      (sourceLift j) ⟨g, le_source j hg⟩).unop.asHom ≫
        (ι quasiEtale ρ).map (cover.arrow j) =
      (ι quasiEtale ρ).map (cover.arrow j) ≫
        (liftAction (U := (ι quasiEtale ρ).obj (compactLiftBasisObject ρ i))
          targetLift ⟨g, le_target hg⟩).unop.asHom

/-- Retain the compatible action data of an actual common-subgroup refinement. -/
def compactCompatibleCoverOfRefinement (i : CompactLiftBasis ρ)
    (l : ActionLift ρ (compactLiftBasisObject ρ i).hom)
    {S : Sieve (compactLiftBasisObject ρ i)}
    (d : CommonSubgroupRefinement
      (fun U : QuasiEtaleSite X => IsCompactSpace U.left) (quasiEtaleTopology X)
      (liftAction (U := (ι quasiEtale ρ).obj (compactLiftBasisObject ρ i)) l) S) :
    CompactCompatibleCover ρ i where
  cover := {
    size := d.size
    index := fun j => ⟨d.obj j, d.admissible j, ⟨d.lift j⟩⟩
    arrow := d.arrow
    covering := d.covering
  }
  targetLift := l
  sourceLift := d.lift
  subgroup := d.subgroup
  le_target := d.le_target
  le_source := d.le_lift
  equivariant := d.equivariant

variable [IsTopologicalGroup G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- For any chosen target lift, compatible compact covers refine every
covering sieve on that target. -/
theorem exists_compactCompatibleCover_refinement (i : CompactLiftBasis ρ)
    (l : ActionLift ρ (compactLiftBasisObject ρ i).hom)
    (S : Sieve (compactLiftBasisObject ρ i))
    (hS : S ∈ quasiEtaleTopology X (compactLiftBasisObject ρ i)) :
    ∃ c : CompactCompatibleCover ρ i,
      c.targetLift = l ∧ ∀ j, S (c.cover.arrow j) := by
  have ha : (compactLiftSystem ρ).IsAdmissible
      ((ι quasiEtale ρ).obj (compactLiftBasisObject ρ i))
      (liftOpenSubgroup (U := (ι quasiEtale ρ).obj (compactLiftBasisObject ρ i)) l)
      (liftAction (U := (ι quasiEtale ρ).obj (compactLiftBasisObject ρ i)) l) := by
    refine ⟨i.property.1, l, le_rfl, ?_⟩
    ext g
    rfl
  obtain ⟨d⟩ := nonempty_commonSubgroupRefinement
    (fun U : QuasiEtaleSite X => IsCompactSpace U.left) (fun _ _ h => h)
    (quasiEtaleTopology X) ha hS
  exact ⟨compactCompatibleCoverOfRefinement ρ i l d, rfl, d.mem⟩

variable (R : Type w) [CommRing R]
variable [LocallySmall.{w} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} R)]

/-- Compatible compact covers support lifting of every coefficient map through
a short exact quotient along the actual degree-zero Čech augmentation. -/
theorem exists_compactCompatibleCover_cech_lift
    [(quasiEtaleTopology X).WEqualsLocallyBijective (ModuleCat.{w} R)]
    (S : ShortComplex (Sheaf (quasiEtaleTopology X) (ModuleCat.{w} R)))
    (hS : S.ShortExact) (i : CompactLiftBasis ρ)
    (l : ActionLift ρ (compactLiftBasisObject ρ i).hom)
    (s : (freeSheafFunctor (quasiEtaleTopology X) R).obj
      (shrinkYoneda.{w}.obj (compactLiftBasisObject ρ i)) ⟶ S.X₃) :
    ∃ (c : CompactCompatibleCover ρ i)
      (t : (freeCechChainComplex (quasiEtaleTopology X) R
        (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))).X 0 ⟶
          S.X₂),
      c.targetLift = l ∧
        t ≫ S.g = (freeCechAugmentation (quasiEtaleTopology X) R
          (c.cover.presheafArrow (quasiEtaleTopology X) (compactLiftBasisObject ρ))).f 0 ≫
            s := by
  have := hS.epi_g
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 inferInstance
  obtain ⟨c, hcl, hc⟩ := exists_compactCompatibleCover_refinement ρ i l _
    (Presheaf.imageSieve_mem (quasiEtaleTopology X) S.g.hom
      (freeRepresentableHomEquiv (quasiEtaleTopology X) R
        (compactLiftBasisObject ρ i) S.X₃ s))
  obtain ⟨t, ht⟩ := c.cover.exists_free_lift_of_imageSieve
    (quasiEtaleTopology X) (compactLiftBasisObject ρ) R S.g s hc
  refine ⟨c,
    (c.cover.freeCechZeroIso (quasiEtaleTopology X) (compactLiftBasisObject ρ) R).hom ≫ t,
    hcl, ?_⟩
  rw [Category.assoc, ht, ← Category.assoc,
    FiniteBasisCover.freeCechZeroIso_hom_augmentation]
  rfl

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
