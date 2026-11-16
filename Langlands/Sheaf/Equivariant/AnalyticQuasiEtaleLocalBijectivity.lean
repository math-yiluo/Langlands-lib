import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Local bijectivity and sheafification on analytic quasi-étale sites -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- On the analytic quasi-étale site, module sheafification in the full
coefficient universe inverts exactly the locally bijective morphisms. -/
abbrev quasiEtale_wEqualsLocallyBijective :
    (quasiEtaleTopology X).WEqualsLocallyBijective
      (ModuleCat.{max u (v + 1) uL} R) := by
  have := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  have := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  have : ∀ Y : (QuasiEtaleSite X)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL}
        (QuasiEtaleSite X)).inverse.op) (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (quasiEtaleTopology X) (A := ModuleCat.{max u (v + 1) uL} R)

variable {G : Type z} [Group G] (ρ : G →* Aut X)
variable [Small.{max u (v + 1) uL} G]

/-- The same characterization holds on the twisted quasi-étale site. -/
abbrev twistedQuasiEtale_wEqualsLocallyBijective :
    (twistedQuasiEtaleTopology ρ).WEqualsLocallyBijective
      (ModuleCat.{max u (v + 1) uL} R) := by
  have := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X ρ
  have := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  have : ∀ Y : (TwistedOver (quasiEtale (K := K)) ρ)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL}
        (TwistedOver (quasiEtale (K := K)) ρ)).inverse.op)
          (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (twistedQuasiEtaleTopology ρ) (A := ModuleCat.{max u (v + 1) uL} R)

end Langlands.Sheaf.Equivariant.Analytic
