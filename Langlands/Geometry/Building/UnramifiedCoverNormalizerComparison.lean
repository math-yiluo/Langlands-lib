import Langlands.Geometry.Building.IntegerValuationCoverSourceData
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylStatement
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Transport of the unramified simply connected normalizer bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom]
    (B : IntegerValuationBuildingData v G) (D : IntegerValuationBuildingData v C)
    (f : normalizerPoints D.i →* normalizerPoints B.i)
    (e : D.Apartment ≃ᵃ[ℝ] B.Apartment)

/-- Equivariance identifies the supplied original actions under affine conjugation. -/
theorem affineConjugation_normalizerAffineEquiv_of_equivariant
    (he : ∀ (m : normalizerPoints D.i) (x : D.Apartment), e (m • x) = f m • e x)
    (m : normalizerPoints D.i) :
    AffineRootSystem.affineConjugation e (D.apartment.normalizerAffineEquiv m) =
      B.apartment.normalizerAffineEquiv (f m) := by
  apply AffineEquiv.ext
  intro x
  change e (m • e.symm x) = f m • x
  rw [he, e.apply_symm_apply]

end IntegerValuationBuildingData

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F G) (B : MaximalUnramified.BuildingData F G)

/-- The actual source building transfers the simply connected normalizer assertion
into the ambient normalizer intersection, without any extra comparison hypotheses. -/
theorem simplyConnectedNormalizer_map_le_affineWeylGroup_of_statement
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    (E.simplyConnectedImage.subgroupOf (normalizerPoints B.i)).map
        B.apartment.normalizerAffineEquiv ≤
      AffineRootSystem.affineWeylGroup B.affineRoots := by
  have : IsAffineHom E.C.X.hom :=
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let D := B.derivedCoverSourceData E.isSimplyConnectedDerivedCover
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨m, hm⟩ := D.lifts n hn
  have hw : D.building.apartment.normalizerAffineEquiv m ∈
      AffineRootSystem.affineWeylGroup D.building.affineRoots := by
    rw [← hsc F E.C
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected D.building]
    exact ⟨m, rfl⟩
  have hmap :
      AffineRootSystem.affineConjugation D.apartmentEquiv
          (D.building.apartment.normalizerAffineEquiv m) ∈
        (AffineRootSystem.affineWeylGroup D.building.affineRoots).map
          (AffineRootSystem.affineConjugation D.apartmentEquiv).toMonoidHom :=
    ⟨D.building.apartment.normalizerAffineEquiv m, hw, rfl⟩
  rw [AffineRootSystem.map_affineWeylGroup_of_transportedRoots_eq
      D.apartmentEquiv D.transportedRoots_eq,
    B.affineConjugation_normalizerAffineEquiv_of_equivariant
      D.building D.normalizerHom D.apartmentEquiv D.equivariant, hm] at hmap
  exact hmap

/-- Elementwise form of the transferred upper inclusion. -/
theorem normalizer_mem_affineWeylGroup_of_mem_simplyConnectedImage
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    (n : normalizerPoints B.i) (hn : (n : rationalPoints G) ∈ E.simplyConnectedImage) :
    B.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  E.simplyConnectedNormalizer_map_le_affineWeylGroup_of_statement B hsc ⟨n, hn, rfl⟩

/-- The original action restricted to the actual simply connected normalizer
intersection, with codomain the affine Weyl subgroup. -/
def simplyConnectedImageNormalizerWeylActionOfStatement
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    E.simplyConnectedImage.subgroupOf (normalizerPoints B.i) →*
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  (B.apartment.normalizerAffineEquiv.comp
    (E.simplyConnectedImage.subgroupOf (normalizerPoints B.i)).subtype).codRestrict _
      (fun n => E.normalizer_mem_affineWeylGroup_of_mem_simplyConnectedImage
        B hsc n n.property)

@[simp]
theorem simplyConnectedImageNormalizerWeylActionOfStatement_coe
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    (n : E.simplyConnectedImage.subgroupOf (normalizerPoints B.i)) :
    (E.simplyConnectedImageNormalizerWeylActionOfStatement B hsc n :
      B.Apartment ≃ᵃ[ℝ] B.Apartment) = B.apartment.normalizerAffineEquiv n :=
  rfl

end UnramifiedZeroDatum

end Langlands.Geometry.Building
