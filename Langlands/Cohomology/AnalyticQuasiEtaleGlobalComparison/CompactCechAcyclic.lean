import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactCechSystem
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Reduction
import Langlands.Cohomology.SiteCech.FreeSections
import Langlands.Cohomology.SiteCech.FiniteCechAcyclic

/-! # Compact compatible Čech systems and actual derived sections -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech
open ZeroObject

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

variable [LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]
variable [EnoughInjectives
  (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))]
variable [(quasiEtaleTopology X).WEqualsLocallyBijective
  (ModuleCat.{max u (v + 1) uL} R)]

/-- Linear Hom from a compact free representable is the actual sections
functor, in the full coefficient universe of the comparison statement. -/
def compactLiftSectionsIso (i : CompactLiftBasis ρ) :
    (linearCoyoneda R
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))).obj
        (op ((freeSheafFunctor (quasiEtaleTopology X) R).obj
          (shrinkYoneda.{max u (v + 1) uL}.obj (compactLiftBasisObject ρ i)))) ≅
      sheafSectionsModule (quasiEtaleTopology X) R (compactLiftBasisObject ρ i) :=
  NatIso.ofComponents
    (fun F => (freeRepresentableHomLinearEquiv
      (quasiEtaleTopology X) R (compactLiftBasisObject ρ i) F).toModuleIso)
    (by
      intro F F' g
      ext f
      rfl)

/-- The compact free-representable description commutes with every
right-derived degree. -/
def compactLiftSectionsDerivedIso (i : CompactLiftBasis ρ) (q : ℕ) :
    ((linearCoyoneda R
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))).obj
        (op ((freeSheafFunctor (quasiEtaleTopology X) R).obj
          (shrinkYoneda.{max u (v + 1) uL}.obj
            (compactLiftBasisObject ρ i))))).rightDerived q ≅
      sectionsDerived (quasiEtaleTopology X) R (compactLiftBasisObject ρ i) q where
  hom := NatTrans.rightDerived (compactLiftSectionsIso.{u, v, uL, z} ρ R i).hom q
  inv := NatTrans.rightDerived (compactLiftSectionsIso.{u, v, uL, z} ρ R i).inv q
  hom_inv_id := by
    dsimp only [sectionsDerived]
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    dsimp only [sectionsDerived]
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

variable (p : ∀ i (c : CompactCompatibleCover ρ i),
  c.cover.CechPresentation (quasiEtaleTopology X) (compactLiftBasisObject ρ))

/-- Positive Hom exactness for the actual compatible-cover system implies
vanishing of higher sections on every compact object admitting a lift. -/
theorem isZero_compactLiftSectionsDerived_of_homAcyclic
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : (compactCompatibleCechSystem ρ R p).HomAcyclic R F)
    (i : CompactLiftBasis ρ) (n : ℕ) :
    IsZero ((sectionsDerived (quasiEtaleTopology X) R
      (compactLiftBasisObject ρ i) (n + 1)).obj F) :=
  ((compactCompatibleCechSystem ρ R p).derivedHomAcyclic_of_homAcyclic
    R F hF i n).of_iso
      ((compactLiftSectionsDerivedIso.{u, v, uL, z} ρ R i (n + 1)).app F).symm

/-- The actual higher-derived sections module identified with zero. -/
def compactCompatibleSectionsZeroIso
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : (compactCompatibleCechSystem ρ R p).HomAcyclic R F)
    (i : CompactLiftBasis ρ) (n : ℕ) :
    ((sectionsDerived (quasiEtaleTopology X) R
      (compactLiftBasisObject ρ i) (n + 1)).obj F) ≅ 0 :=
  (isZero_compactLiftSectionsDerived_of_homAcyclic.{u, v, uL, z} ρ R p F hF i n).isoZero

variable [Small.{max u (v + 1) uL} G]

/-- Hom exactness for restrictions of injective equivariant coefficients
supplies the published ordinary cohomological acyclicity target. -/
theorem restrictedInjectivesAcyclic_of_compactCompatibleCech
    (h : IsCompactSpace X → IsContinuousAction ρ →
      ∀ I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R), Injective I →
        (compactCompatibleCechSystem ρ R p).HomAcyclic R
          ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)) :
    QuasiEtaleRestrictedInjectivesAcyclicStatement.{u, v, uL, z} X G ρ R := by
  intro hX hρ I hI q
  exact isZero_compactLiftSectionsDerived_of_homAcyclic.{u, v, uL, z} ρ R p _
    (h hX hρ I hI) (compactLiftBasisIdentity ρ hX hρ) q

/-- The comparison follows once all-degree finite nerve presentations and
restricted-injective positive Hom exactness have been established. -/
theorem analyticQuasiEtaleGlobalComparison_of_compactCompatibleCech
    (h : IsCompactSpace X → IsContinuousAction ρ →
      ∀ I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R), Injective I →
        (compactCompatibleCechSystem ρ R p).HomAcyclic R
          ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)) :
    AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R :=
  analyticQuasiEtaleGlobalComparison_of_restrictedInjectivesAcyclic.{u, v, uL, z} ρ R
    (restrictedInjectivesAcyclic_of_compactCompatibleCech.{u, v, uL, z} ρ R p h)

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
