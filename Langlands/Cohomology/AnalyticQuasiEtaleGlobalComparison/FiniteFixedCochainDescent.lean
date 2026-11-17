import Langlands.Cohomology.SiteCech.EquivariantCochainDescent
import Langlands.Cohomology.SiteCech.FreeSections
import Langlands.Sheaf.Equivariant.AnalyticFiniteFixedSections
import Langlands.Sheaf.Equivariant.AnalyticSubgroupInjectives
import Langlands.Sheaf.Equivariant.AnalyticSubgroupRefinements

/-! # Finite fixed sections and equivariant descent of Čech cocycles -/

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
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]

local instance (S : Type w) [CommRing S]
    [HasSheafify (quasiEtaleTopology X) (ModuleCat.{w} S)] (m : ℕ) :
    HasColimitsOfShape (Discrete (Fin m))
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{w} S)) :=
  Sheaf.instHasColimitsOfShape

/-- The actual section family represented by a cochain on a finite coproduct
of free representable sheaves. -/
def finiteFreeCochainSections {m : ℕ} (U : Fin m → QuasiEtaleSite X)
    {M : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)}
    (e : M ≅ ∐ (fun i => (freeSheafFunctor (quasiEtaleTopology X) R).obj
      (shrinkYoneda.{max u (v + 1) uL}.obj (U i))))
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (x : M ⟶ F) : ∀ i, F.obj.obj (op (U i)) :=
  fun i => freeRepresentableHomEquiv (quasiEtaleTopology X) R (U i) F
    (Sigma.ι (fun j => (freeSheafFunctor (quasiEtaleTopology X) R).obj
      (shrinkYoneda.{max u (v + 1) uL}.obj (U j))) i ≫ e.inv ≫ x)

/-- One open subgroup simultaneously fixes all sections of a specified finite
free cochain, below a prescribed bound and all supplied lifting subgroups. -/
def finiteCochainFixedSections
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    {m : ℕ} (U : Fin m → QuasiEtaleSite X)
    (l : ∀ i, ActionLift ρ (U i).hom) (hU : ∀ i, IsCompactSpace (U i).left)
    {M : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)}
    (e : M ≅ ∐ (fun i => (freeSheafFunctor (quasiEtaleTopology X) R).obj
      (shrinkYoneda.{max u (v + 1) uL}.obj (U i))))
    (x : M ⟶ (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)
    (Q : OpenSubgroup G) :
    CommonFixedSections I.obj.obj (fun i => (ι quasiEtale ρ).obj (U i))
      (fun i => liftOpenSubgroup (l i)) (fun i => liftAction (l i))
      (finiteFreeCochainSections.{u, v, uL} R U e _ x) Q :=
  finiteLiftFixedSections (fun U => IsCompactSpace U.left) I.obj.obj I.property
    U l hU (finiteFreeCochainSections.{u, v, uL} R U e _ x) Q

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- An exact model of an ordinary cochain in the discrete sheaf category of an
open subgroup, with the actual subgroup restriction of its coefficient. -/
abbrev OpenSubgroupCochainLift
    (P : ChainComplex
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) ℕ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (H : OpenSubgroup G) (n : ℕ)
    (x : P.X (n + 1) ⟶ (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I) :=
  haveI := hasFiniteEquivariantRefinements_compactLiftSystem_subgroup
    (ρ := ρ) H.isOpen
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X
    (ρ.comp (H : Subgroup G).subtype) R
  haveI : (quasiEtaleGSheafRestriction.{u, v, uL}
      (ρ.comp (H : Subgroup G).subtype) R).Faithful :=
    inferInstanceAs (discreteRestriction (quasiEtaleTopology X) R
      (compactLiftSystem (ρ.comp (H : Subgroup G).subtype))).Faithful
  haveI := quasiEtaleGSheafRestriction_additive.{u, v, uL}
    (ρ.comp (H : Subgroup G).subtype) R
  EquivariantCochainLift
    (quasiEtaleGSheafRestriction.{u, v, uL} (ρ.comp (H : Subgroup G).subtype) R)
    P ((quasiEtaleGSheafSubgroupRestriction ρ
      (ModuleCat.{max u (v + 1) uL} R) H.isOpen).obj I) _
    ((quasiEtaleGSheafSubgroupRestrictionCompRestrictionIso.{u, v, uL}
      ρ R H.isOpen).app I) n x

/-- Fixed-cochain models imply exactness in the specified positive degree.
The exact models and their equivariant lifts are geometric input; the finite
fixing subgroup and injectivity of the restricted coefficient are proved here. -/
theorem exactAt_of_finiteFixedCochainModels
    (P : ChainComplex
      (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) ℕ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I]
    (n : ℕ) {m : ℕ} (U : Fin m → QuasiEtaleSite X)
    (l : ∀ i, ActionLift ρ (U i).hom) (hU : ∀ i, IsCompactSpace (U i).left)
    (e : P.X (n + 1) ≅ ∐ (fun i => (freeSheafFunctor (quasiEtaleTopology X) R).obj
      (shrinkYoneda.{max u (v + 1) uL}.obj (U i))))
    (Q : OpenSubgroup G)
    (model : ∀ (N : CommonOpenSubgroup Q (fun i => liftOpenSubgroup (l i)))
      (x : P.X (n + 1) ⟶ (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I),
      finiteFreeCochainSections.{u, v, uL} R U e _ x ∈
        fixedFamilySubmodule I.obj.obj (fun i => liftAction (l i)) N.val →
      Nonempty (OpenSubgroupCochainLift.{u, v, uL, z} ρ R P I N.val n x)) :
    (P.linearYonedaObj R
      ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change P.d (n + 2) (n + 1) ≫ x = 0 at hx
  let d := finiteCochainFixedSections.{u, v, uL, z} ρ R I U l hU e x Q
  let N : CommonOpenSubgroup Q (fun i => liftOpenSubgroup (l i)) :=
    ⟨d.subgroup, d.le_bound, d.le_action⟩
  obtain ⟨L⟩ := model N x d.fixes
  have := hasFiniteEquivariantRefinements_compactLiftSystem_subgroup
    (ρ := ρ) N.val.isOpen
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X
    (ρ.comp (N.val : Subgroup G).subtype) R
  have : (quasiEtaleGSheafRestriction.{u, v, uL}
      (ρ.comp (N.val : Subgroup G).subtype) R).Faithful :=
    inferInstanceAs (discreteRestriction (quasiEtaleTopology X) R
      (compactLiftSystem (ρ.comp (N.val : Subgroup G).subtype))).Faithful
  have := quasiEtaleGSheafRestriction_additive.{u, v, uL}
    (ρ.comp (N.val : Subgroup G).subtype) R
  have := quasiEtaleGSheafSubgroupRestriction_preservesInjectiveObjects.{u, v, uL, z}
    ρ N.val.isOpen R
  have : Injective ((quasiEtaleGSheafSubgroupRestriction ρ
      (ModuleCat.{max u (v + 1) uL} R) N.val.isOpen).obj I) := inferInstance
  exact L.exists_primitive hx

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
