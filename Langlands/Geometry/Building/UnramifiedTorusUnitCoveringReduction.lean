import Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Covering by fixed apartments from the two torus-unit geometric inputs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The two geometric unit-fixed-point inputs imply the exact rational covering
statement, using rational conjugacy of maximal split tori. -/
def UnramifiedTorusUnitCoveringReductionStatement : Prop :=
  UnramifiedFixedPointSplitTorusStatement.{u} →
  UnramifiedTorusUnitFixedApartmentStatement.{u} →
  UnramifiedGaloisFixedBuildingPointStatement.{u}

/-- Move the prescribed point to the unit-fixed locus of the chosen split torus
by a rational conjugator, then apply the special-apartment fixed-locus input. -/
theorem unramifiedTorusUnitCoveringReduction :
    UnramifiedTorusUnitCoveringReductionStatement.{u} := by
  intro hCover hUnit F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (baseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD y hy
  obtain ⟨S', iS', hiS', hyUnits⟩ := hCover F G hG T iT hiT D C h6 hD y hy
  obtain ⟨g, e, he⟩ := smoothMaximalSplitTorusConjugacy F G S S' iS iS' hiS hiS'
  let z : D.ReducedBuilding := (rationalExtend F (inertiaFixedField F) G g)⁻¹ • y
  have hz : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ z = z := by
    intro σ
    dsimp only [z]
    rw [KPApartmentData.galoisQuotientAction_smul, map_inv,
      Langlands.GroupScheme.GaloisPointComparison.rationalConjugate_rationalExtend, hy σ]
  have hzUnits : IsFixedByUnramifiedTorusUnits F iS z :=
    IsFixedByScalarTorusUnits.conjugate (MaximalUnramified.valuation F)
      iS iS' e.hom g he hyUnits
  obtain ⟨x, hx, hxy⟩ := hUnit F G hG S iS hiS T iT f hf hiT D C h6 hD z hz hzUnits
  refine ⟨g, x, hx, ?_⟩
  rw [hxy]
  exact smul_inv_smul _ _

end Langlands.Geometry.Building
