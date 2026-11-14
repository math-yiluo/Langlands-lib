import Langlands.Sheaf.Equivariant.AnalyticEtaleRepCohomology
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRepCohomology
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison
import Langlands.Sheaf.Equivariant.TwistedRepComparison

/-!
# Equivariance of the comparison maps for étale and quasi-étale `G`-sheaves

Let `G` act on an analytic space `X` and let `F` be an étale (or quasi-étale) `G`-sheaf of
modules. Berkovich's comparison maps `H^q(X{G}, F) → H^q(X, b^*F)` (Theorem 1.6.1(ii)) and
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` (Corollary 1.5.2(i)) are `etaleComparison`,
`etaleCompactComparison`, `quasiEtaleComparison` and `quasiEtaleCompactComparison`. The
targets carry the canonical actions of `G` of `AnalyticEtaleRepCohomology` and
`AnalyticQuasiEtaleRepCohomology`. This module proves that each comparison map carries the
action of `g ∈ G` on `H^q(X{G}, F)` (resp. `H^q_c(X{G}, F)`) to the action of `g` on
`H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`). The proofs specialize `TwistedRepComparison`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section EtaleGlobal

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` for an étale `G`-sheaf `F` carries the
action of `g` on `H^q(X{G}, F)` to the canonical action of `g` on `H^q(X, b^*F)`. -/
theorem etaleComparison_representation (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (etaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G).obj F) :
    ((etaleComparison.{u, v, uL} ρ R q).app F).hom
        (((etaleGSheafCohomology.{u, v, uL} ρ R q).obj F).representation g x) =
      etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F g
        (((etaleComparison.{u, v, uL} ρ R q).app F).hom x) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have h₁ := exactGlobalComparison_app_representation (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedEtaleTopology ρ)) q F g x
  have h₂ := exactGlobalComparison_app_apply (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedEtaleTopology ρ)) q F x
  refine h₁.trans ?_
  rw [show ((etaleComparison.{u, v, uL} ρ R q).app F).hom x = _ from h₂]
  exact (etaleRestrictionCohomologyAction_apply.{u, v, uL} ρ R q F g _).symm

end EtaleGlobal

section EtaleCompact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` for an étale `G`-sheaf `F`, with
supports in the `L`-valued points, carries the action of `g` on `H^q_c(X{G}, F)` to the
canonical action of `g` on `H^q_c(X, b^*F)`. -/
theorem etaleCompactComparison_representation (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G).obj F) :
    ((etaleCompactComparison L ρ h R q).app F).hom
        (((etaleGSheafCompactCohomology L ρ h R q).obj F).representation g x) =
      etaleRestrictionCompactCohomologyAction L ρ h R q F g
        (((etaleCompactComparison L ρ h R q).app F).hom x) := by
  let _ := pointTopology L X
  let _ := EtaleSite.pointAction L ρ
  have := continuousConstSMul_pointAction L ρ
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have h₁ := exactCompactComparison_app_representation (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedEtaleTopology ρ)) (EtaleSite.pointEquivariance L ρ h) q F g x
  have h₂ := exactCompactComparison_app_apply (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedEtaleTopology ρ)) (EtaleSite.pointEquivariance L ρ h) q F x
  refine h₁.trans ?_
  rw [show ((etaleCompactComparison L ρ h R q).app F).hom x = _ from h₂]
  exact (etaleRestrictionCompactCohomologyAction_apply L ρ h R q F g _).symm

end EtaleCompact

section QuasiEtaleGlobal

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` for a quasi-étale `G`-sheaf `F` carries the
action of `g` on `H^q(X{G}, F)` to the canonical action of `g` on `H^q(X, b^*F)`. -/
theorem quasiEtaleComparison_representation (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G).obj F) :
    ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom
        (((quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F).representation g x) =
      quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F g
        (((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom x) := by
  have := quasiEtale_hasSheafify.{u, v, uL} X R
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  have := quasiEtale_enoughInjectives.{u, v, uL} X R
  have := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  have h₁ := exactGlobalComparison_app_representation (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedQuasiEtaleTopology ρ)) q F g x
  have h₂ := exactGlobalComparison_app_apply (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedQuasiEtaleTopology ρ)) q F x
  refine h₁.trans ?_
  rw [show ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom x = _ from h₂]
  exact (quasiEtaleRestrictionCohomologyAction_apply.{u, v, uL} ρ R q F g _).symm

end QuasiEtaleGlobal

section QuasiEtaleCompact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` for a quasi-étale `G`-sheaf `F`, with
supports in the `L`-valued points, carries the action of `g` on `H^q_c(X{G}, F)` to the
canonical action of `g` on `H^q_c(X, b^*F)`. -/
theorem quasiEtaleCompactComparison_representation (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G).obj F) :
    ((quasiEtaleCompactComparison L ρ h R q).app F).hom
        (((quasiEtaleGSheafCompactCohomology L ρ h R q).obj F).representation g x) =
      quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F g
        (((quasiEtaleCompactComparison L ρ h R q).app F).hom x) := by
  let _ := pointTopology L X
  let _ := EtaleSite.pointAction L ρ
  have := continuousConstSMul_pointAction L ρ
  have := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  have := quasiEtale_hasSheafify.{u, v, uL} X R
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  have := quasiEtale_enoughInjectives.{u, v, uL} X R
  have := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  have h₁ := exactCompactComparison_app_representation (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedQuasiEtaleTopology ρ)) (QuasiEtaleSite.pointEquivariance L ρ h) q F g x
  have h₂ := exactCompactComparison_app_apply (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
      (twistedQuasiEtaleTopology ρ)) (QuasiEtaleSite.pointEquivariance L ρ h) q F x
  refine h₁.trans ?_
  rw [show ((quasiEtaleCompactComparison L ρ h R q).app F).hom x = _ from h₂]
  exact (quasiEtaleRestrictionCompactCohomologyAction_apply L ρ h R q F g _).symm

end QuasiEtaleCompact

end Langlands.Sheaf.Equivariant.Analytic
