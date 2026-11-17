import Langlands.Sheaf.Equivariant.AnalyticPointProductCutoffs
import Langlands.Sheaf.CompactExtensionUniverseLift

/-! # Ordinary compact softness of actual analytic smooth point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL z

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct
open TwistedOver

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable {R : Type (max u (v + 1) uL)} [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable (M : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
  ModuleCat.{max u (v + 1) uL} R)

/-- Actual induction, the existing locally discrete subsheaf, and actual étale
restriction, applied to independent Godement point coefficients. -/
def etaleRestrictedSmoothPointProduct :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  (TwistedOver.restriction ρ (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj
    ((LocalActionSystem.smoothSubsheafFunctor (distinguishedLiftSystem ρ)
      (twistedEtaleTopology ρ)).obj
        ((TwistedOver.induction ρ (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj
          (productSheaf (etaleGodementPoints.{u, v, uL} L h)
            (ModuleCat.{max u (v + 1) uL} R) M)))

/-- The actual ordinary restriction has the compact-neighborhood extension
property, before any universe lift or cohomological comparison. -/
theorem hasCompactExtensions_etaleRestrictedSmoothPointProduct
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ) :
    Langlands.Sheaf.CompactExtension.HasCompactExtensions
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
        (etaleRestrictedSmoothPointProduct L h ρ M)) := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  intro C hC U hCU s
  change ↥(LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ)
    (twistedEtaleTopology ρ) (etaleRawInducedPointProduct L h ρ M)
      ((ι etale ρ).obj (openEtaleObject X U))) at s
  obtain ⟨V, hVU, t, hCV, -, hVc, ht, heq, hz⟩ :=
    exists_etaleSmoothPointProduct_compact_extension L h ρ M hρ hC U hCU s.val s.property
  let S := etaleRestrictedSmoothPointProduct L h ρ M
  let t' : S.obj.obj (op (etaleSelf X)) := ⟨t, ht⟩
  let g := (etaleUnderlyingGlobalIso X S).hom t'
  refine ⟨V, homOfLE hVU, g, hCV, hVc, ?_, ?_⟩
  · change ((etaleUnderlyingSheaf X (ModuleCat R)).obj S).obj.map
        (homOfLE le_top : V ⟶ ⊤).op ((etaleUnderlyingGlobalIso X S).hom t') = _
    rw [etaleUnderlyingGlobalIso_restrict.{u, v, uL}]
    apply Subtype.ext
    exact heq
  · change ((etaleUnderlyingSheaf X (ModuleCat R)).obj S).obj.map
        (homOfLE le_top :
          Langlands.Sheaf.CompactExtension.outsideClosure V ⟶ ⊤).op
        ((etaleUnderlyingGlobalIso X S).hom t') = 0
    rw [etaleUnderlyingGlobalIso_restrict.{u, v, uL}]
    apply Subtype.ext
    exact hz

/-- The ordinary sheaf on the canonically lifted underlying space is c-soft
for arbitrary independent coefficients. -/
theorem isCSoft_universeLift_etaleRestrictedSmoothPointProduct
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ) :
    Langlands.Sheaf.CompactSoft.IsCSoft
      (Langlands.Sheaf.CompactExtension.universeLift.{v, max u (v + 1) uL}
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
          (etaleRestrictedSmoothPointProduct L h ρ M))) :=
  Langlands.Sheaf.CompactExtension.isCSoft_universeLift _
    (hasCompactExtensions_etaleRestrictedSmoothPointProduct L h ρ M hρ)

end Langlands.Sheaf.Equivariant.Analytic
