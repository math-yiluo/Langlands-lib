import Langlands.GroupScheme.IntegralModel.SpecialStabilizerStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerStatement
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement

/-! # The building comparison from its maximal unramified form and descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

set_option maxHeartbeats 800000 in
/-- The maximal unramified special-stabilizer identity and unramified descent of
the existing building quotient together give the base-field special-stabilizer
identity on every axiom-satisfying building datum. -/
theorem specialStabilizerStatement_of_unramified
    (hstab : UnramifiedSpecialStabilizerStatement.{u})
    (hdesc : UnramifiedBuildingDescentStatement.{u}) :
    SpecialStabilizerStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial P _ _ _ _ _ _ _ _ _
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨C, D, e, hinj, he, hfix, hspec⟩ := hdesc F G hG P.toValuationBuildingData
  obtain ⟨x, hx, hM, hunique⟩ := hstab F G hG M hspecial C
  have hxfix : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      g ∈ M.baseChangeUnramified.integralPoints → g • x = x := by
    intro g hg
    rw [hM] at hg
    exact (C.mem_oneStabilizer.mp hg).2
  obtain ⟨z, hz⟩ := hfix x (by
    intro σ
    exact M.unramifiedIntegralImage_semilinearAction_eq_of_unique_fixed C D x hxfix
      hunique σ)
  subst hz
  refine ⟨z, hspec z hx, ?_⟩
  -- Restate the equivariance through the reducible abbreviation `UnramifiedClosure`
  -- used by the descent lemma; unifying the two forms directly is slow.
  have he' : ∀ (g : rationalPoints G) (w : P.ReducedBuilding),
      e (g • w) = rationalExtend F (UnramifiedClosure F) G g • e w := he
  exact M.integralPoints_eq_compactStabilizer_of_unramified P.toValuationBuildingData C e
    hinj he' z hM

/-- The building construction, the maximal unramified special-stabilizer identity
and unramified descent of the existing building quotient together imply the
exact supplied-model building comparison target. -/
def BuildingComparisonUnramifiedReductionStatement : Prop :=
  RootValuationBuildingConstructionStatement.{u} →
    UnramifiedSpecialStabilizerStatement.{u} →
      UnramifiedBuildingDescentStatement.{u} →
        BuildingComparisonStatement.{u}

/-- The building construction, the maximal unramified special-stabilizer identity
and unramified descent together give the exact published comparison target. -/
theorem buildingComparisonStatement_of_unramified
    (hcon : RootValuationBuildingConstructionStatement.{u})
    (hstab : UnramifiedSpecialStabilizerStatement.{u})
    (hdesc : UnramifiedBuildingDescentStatement.{u}) :
    BuildingComparisonStatement.{u} :=
  buildingComparisonStatement_of_specialStabilizer hcon
    (specialStabilizerStatement_of_unramified hstab hdesc)

/-- Proof of the reduction statement. -/
theorem buildingComparisonUnramifiedReduction :
    BuildingComparisonUnramifiedReductionStatement.{u} :=
  fun hcon hstab hdesc => buildingComparisonStatement_of_unramified hcon hstab hdesc

end Langlands.GroupScheme.IntegralModel
