import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.FiniteFixedCochainDescent
import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableCochain

/-! # Finite free models for analytic open-subgroup cochain descent -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech
open Langlands.Cohomology.DiscreteSheafDerivedComparison

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]

local instance (S : Type w) [CommRing S]
    [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} S)] (m : ℕ) :
    HasColimitsOfShape (Discrete (Fin m))
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{w} S)) :=
  Sheaf.instHasColimitsOfShape

/-- The finite signed free model in the actual lift system of an open
subgroup acting on the original quasi-etale site. -/
abbrev OpenSubgroupFiniteFreeThreeTermModel
    (P : ChainComplex
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) ℕ)
    (H : OpenSubgroup G) (n : ℕ) :=
  GlobalLift.FiniteFreeThreeTermModel (quasiEtaleTopology X) R
    (compactLiftSystem (ρ.comp (H : Subgroup G).subtype)) P n

namespace OpenSubgroupFiniteFreeThreeTermModel

variable {ρ R}
variable {P : ChainComplex
  (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) ℕ}
variable {H : OpenSubgroup G} {n : ℕ}
variable (M : OpenSubgroupFiniteFreeThreeTermModel.{u, v, uL, z} ρ R P H n)
variable (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
variable (x : P.X (n + 1) ⟶ (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)

/-- The original coefficient sections specified by the middle comparison
isomorphism of the finite model and the given ordinary cochain. -/
def cochainSections :
    ∀ i, I.obj.obj.obj (op ((ι quasiEtale ρ).obj (M.middle i).obj)) :=
  finiteFreeCochainSections.{u, v, uL} R (fun i => (M.middle i).obj)
    M.middleIso.symm _ x

/-- The precise middle cochain sections are fixed by the normalized model
actions, after mapping those actions to the original twisted site. -/
def FixesCochain : Prop :=
  ∀ i (g : (H : Subgroup G)),
    I.obj.obj.map ((subgroupInclusion ρ (H : Subgroup G)).map
      ((M.middle i).action g).unop).op (M.cochainSections I x i) =
        M.cochainSections I x i

/-- Original-coefficient fixedness produces the actual fixed sections of the
subgroup-restricted coefficient, with no change of their values. -/
def fixedSections (hfix : M.FixesCochain I x) (i : Fin M.middleSize) :
    (M.middle i).FixedSections
      (((quasiEtaleGSheafSubgroupRestriction ρ
        (ModuleCat.{max u (v + 1) uL} R) H.isOpen).obj I).obj.obj ⋙
          forget (ModuleCat.{max u (v + 1) uL} R)) :=
  ⟨M.cochainSections I x i, hfix i⟩

@[simp]
theorem fixedSections_val (hfix : M.FixesCochain I x) (i : Fin M.middleSize) :
    (M.fixedSections I x hfix i).val = M.cochainSections I x i := rfl

variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- An exact ordinary segment and a finite signed model fixing the precise
middle sections give an exact open-subgroup lift of that ordinary cochain. -/
def cochainLift (hP : P.ExactAt (n + 1)) (hfix : M.FixesCochain I x) :
    OpenSubgroupCochainLift.{u, v, uL, z} ρ R P I H n x := by
  haveI := hasFiniteEquivariantRefinements_compactLiftSystem_subgroup
    (ρ := ρ) H.isOpen
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X
    (ρ.comp (H : Subgroup G).subtype) R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    (ρ.comp (H : Subgroup G).subtype) R
  let I' := (quasiEtaleGSheafSubgroupRestriction ρ
    (ModuleCat.{max u (v + 1) uL} R) H.isOpen).obj I
  let e := (quasiEtaleGSheafSubgroupRestrictionCompRestrictionIso.{u, v, uL}
    ρ R H.isOpen).app I
  have he : e.inv = 𝟙 ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I) := rfl
  exact GlobalLift.FiniteFreeThreeTermModel.cochainLift
    (quasiEtaleTopology X) R (compactLiftSystem (ρ.comp (H : Subgroup G).subtype))
    (isLiftSystem_liftSystem _) M hP I' _ e x (M.fixedSections I x hfix)
    (fun i => by
      simp only [fixedSections_val, cochainSections, finiteFreeCochainSections,
        Iso.symm_inv]
      rw [he]
      erw [Category.comp_id]
      rfl)

end OpenSubgroupFiniteFreeThreeTermModel

variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- Actual finite signed models fixing the middle sections of each cocycle
imply exactness against an injective quasi-etale coefficient. The ordinary
segment exactness and finite models remain explicit inputs. -/
theorem exactAt_of_openSubgroupFiniteFreeModels
    (P : ChainComplex
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) ℕ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I]
    (n : ℕ) (hP : P.ExactAt (n + 1))
    (model : ∀ (x : P.X (n + 1) ⟶
      (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I),
      P.d (n + 2) (n + 1) ≫ x = 0 →
      ∃ (H : OpenSubgroup G) (M : OpenSubgroupFiniteFreeThreeTermModel.{u, v, uL, z} ρ R P H n),
        M.FixesCochain I x) :
    (P.linearYonedaObj R
      ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change P.d (n + 2) (n + 1) ≫ x = 0 at hx
  obtain ⟨H, M, hfix⟩ := model x hx
  let L := OpenSubgroupFiniteFreeThreeTermModel.cochainLift M I x hP hfix
  have := hasFiniteEquivariantRefinements_compactLiftSystem_subgroup
    (ρ := ρ) H.isOpen
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X
    (ρ.comp (H : Subgroup G).subtype) R
  have : (quasiEtaleGSheafRestriction.{u, v, uL}
      (ρ.comp (H : Subgroup G).subtype) R).Faithful :=
    inferInstanceAs (discreteRestriction (quasiEtaleTopology X) R
      (compactLiftSystem (ρ.comp (H : Subgroup G).subtype))).Faithful
  have := quasiEtaleGSheafRestriction_additive.{u, v, uL}
    (ρ.comp (H : Subgroup G).subtype) R
  have := quasiEtaleGSheafSubgroupRestriction_preservesInjectiveObjects.{u, v, uL, z}
    ρ H.isOpen R
  have : Injective ((quasiEtaleGSheafSubgroupRestriction ρ
      (ModuleCat.{max u (v + 1) uL} R) H.isOpen).obj I) := inferInstance
  exact L.exists_primitive hx

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
