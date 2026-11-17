import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactLiftBasis
import Langlands.Cohomology.SiteCech.FiniteCechPresentation
import Langlands.Geometry.Analytic.ContinuousDomainWidePullbacks

/-! # Actual compact lifted Čech presentations for domain-chart covers -/

noncomputable section

universe u v z w

namespace Langlands.Analytic.SaturatedAtlasPresentation.FiniteCompactDomainChartCover

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology.SiteCech
open Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
  {U : QuasiEtaleSite X} (C : FiniteCompactDomainChartCover U)
  (l : ActionLift ρ U.hom)
  (σ : ∀ i, l.subgroup →* Aut (C.obj i).left)
  (hσ : ∀ i (g : l.subgroup),
    (σ i g).hom ≫ (C.arrow i).left =
      (C.arrow i).left ≫ (l.action g).hom)
  (hcσ : ∀ i, IsContinuousAction (σ i))

/-- Compatible continuous source actions are actual lifts of the base action,
using the same open subgroup as the target lift. -/
def chartSourceActionLift (i : C.Index) : ActionLift ρ (C.obj i).hom where
  subgroup := l.subgroup
  isOpen_subgroup := l.isOpen_subgroup
  action := σ i
  isContinuousAction := hcσ i
  equivariant g := by
    rw [← MorphismProperty.Over.w (C.arrow i), ← Category.assoc, hσ,
      Category.assoc, l.equivariant, ← Category.assoc]

/-- Each selected chart is a compact basis object carrying its actual lift. -/
def chartLiftBasisIndex (i : C.Index) : CompactLiftBasis ρ :=
  ⟨C.obj i, C.compact i, ⟨C.chartSourceActionLift l σ hσ hcσ i⟩⟩

variable [Fintype C.Index]

/-- Reindex the actual chart cover by a finite ordinal, retaining its compact
source objects and the lifts supplied by the compatible actions. -/
def compactLiftBasisCover :
    FiniteBasisCover (quasiEtaleTopology X) (compactLiftBasisObject ρ) U where
  size := Fintype.card C.Index
  index j := C.chartLiftBasisIndex l σ hσ hcσ ((Fintype.equivFin C.Index).symm j)
  arrow j := C.arrow ((Fintype.equivFin C.Index).symm j)
  covering := by
    change Sieve.generate (Presieve.ofArrows
      (C.obj ∘ (Fintype.equivFin C.Index).symm)
      (fun j => C.arrow ((Fintype.equivFin C.Index).symm j))) ∈
        quasiEtaleTopology X U
    rw [Presieve.ofArrows_comp_eq_of_surjective C.arrow
      (Fintype.equivFin C.Index).symm.surjective]
    exact C.generate_mem_quasiEtaleTopology

variable [T2Space (localizedSpaceFunctor.obj U.left)]

/-- A nonempty tuple is represented by the actual compact intersection carrying
the continuous common-subgroup action constructed from the original cover. -/
def tupleLiftBasisIndex (n : ℕ)
    (α : Fin (n + 1) → Fin (Fintype.card C.Index)) : CompactLiftBasis ρ :=
  ⟨C.wideObj (fun j => (Fintype.equivFin C.Index).symm (α j)) 0,
    C.isCompactSpace_wideObj _ _,
    ⟨C.wideActionLift l σ hσ _ _⟩⟩

variable [LocallySmall.{w} (QuasiEtaleSite X)]

/-- Actual compact limiting intersection cones yield a finite representable
presentation in every degree of the domain-cover presheaf Čech nerve. -/
def domainChartCechPresentation :
    (C.compactLiftBasisCover l σ hσ hcσ).CechPresentation
      (quasiEtaleTopology X) (compactLiftBasisObject ρ) :=
  (C.compactLiftBasisCover l σ hσ hcσ).cechPresentationOfCones
    (quasiEtaleTopology X) (compactLiftBasisObject ρ)
    (C.tupleLiftBasisIndex l σ hσ)
    (fun _ α => C.wideCone (fun j => (Fintype.equivFin C.Index).symm (α j)) 0)
    (fun _ α => C.wideIsLimit (fun j => (Fintype.equivFin C.Index).symm (α j)) 0)
    (fun _ _ => Iso.refl _)

end Langlands.Analytic.SaturatedAtlasPresentation.FiniteCompactDomainChartCover
