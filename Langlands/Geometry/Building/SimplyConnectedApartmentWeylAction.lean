import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.FacetFixingWeylReduction
import Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement

/-! # The simply connected normalizer action from facet fixing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Actual root preservation and opposite-pair reflections reduce exact Weyl
image to pointwise fixing of every setwise stabilized facet. -/
theorem normalizerAffineEquiv_range_eq_affineWeylGroup_of_facet_fixing
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (hfix : ∀ Fa : Set B.Apartment, AffineRootSystem.IsFacet B.affineRoots Fa →
      ∀ n : normalizerPoints B.i, (fun x : B.Apartment => n • x) '' Fa = Fa →
        ∀ x ∈ Fa, n • x = x) :
    B.apartment.normalizerAffineEquiv.range =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  AffineRootSystem.range_eq_affineWeylGroup_of_facet_fixing hΨ
    B.apartment.normalizerAffineEquiv
    B.apartment.normalizerAffineEquiv_range_le_rootStabilizer
    (B.affineWeylGroup_le_normalizerAffineEquiv_range_of_isAffineRootSystem hΨ hF) hfix

/-- A proof of the actual simply connected facet-fixing statement implies the
second sentence of AS 5 from AS 3 and opposite-pair existence alone. -/
theorem normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected G)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    B.apartment.normalizerAffineEquiv.range =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.normalizerAffineEquiv_range_eq_affineWeylGroup_of_facet_fixing hΨ hF
    (hfix F G B hsc)

/-- Restrict the actual simply connected normalizer action to the affine Weyl
group using the explicitly supplied facet-fixing result, AS 3 and actual
opposite-pair existence. No AS 5 premise is used. -/
def simplyConnectedNormalizerWeylAction
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected G)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    normalizerPoints B.i →* AffineRootSystem.affineWeylGroup B.affineRoots where
  toFun n := ⟨B.apartment.normalizerAffineEquiv n, by
    rw [← B.normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing
      hfix hsc hΨ hF]
    exact ⟨n, rfl⟩⟩
  map_one' := Subtype.ext (map_one B.apartment.normalizerAffineEquiv)
  map_mul' n m := Subtype.ext (map_mul B.apartment.normalizerAffineEquiv n m)

@[simp]
theorem simplyConnectedNormalizerWeylAction_coe
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected G)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) (n : normalizerPoints B.i) :
    (B.simplyConnectedNormalizerWeylAction hfix hsc hΨ hF n :
        B.Apartment ≃ᵃ[ℝ] B.Apartment) = B.apartment.normalizerAffineEquiv n :=
  rfl

@[simp]
theorem simplyConnectedNormalizerWeylAction_apply
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected G)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) (n : normalizerPoints B.i)
    (x : B.Apartment) :
    (B.simplyConnectedNormalizerWeylAction hfix hsc hΨ hF n :
        B.Apartment ≃ᵃ[ℝ] B.Apartment) x = n • x :=
  rfl

/-- The restricted action reaches every element of the actual reflection-generated
affine Weyl subgroup. -/
theorem simplyConnectedNormalizerWeylAction_surjective
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected G)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    Function.Surjective (B.simplyConnectedNormalizerWeylAction hfix hsc hΨ hF) := by
  intro w
  have hw : (w : B.Apartment ≃ᵃ[ℝ] B.Apartment) ∈
      B.apartment.normalizerAffineEquiv.range := by
    rw [B.normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing
      hfix hsc hΨ hF]
    exact w.property
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, Subtype.ext hn⟩

end Langlands.Geometry.Building.ValuationBuildingData
