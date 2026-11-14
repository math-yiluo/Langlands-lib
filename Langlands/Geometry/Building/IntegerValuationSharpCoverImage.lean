import Langlands.Geometry.Building.KPSharpCoverImageProof
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Sharp fixers in the simply connected image over an integer-valued field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G D C : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {d : D ⟶ G} {π : C ⟶ D}

/-- Actual relative root groups lift through every supplied simply connected
derived cover, over an arbitrary field. -/
theorem rootGroupPoints_le_simplyConnectedImage_of_isMaximalSplitTorus
    (hi : IsMaximalSplitTorus i) (hcover : IsSimplyConnectedDerivedCover d π)
    (α : relativeRoots i) :
    rootGroupPoints i α ≤ simplyConnectedImage d π := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨R, -⟩ := relativeRootReflectionExistence_of_rootRankOneFactorization
    rootRankOneFactorization k G hcover.isConnectedReductive S i hi
  intro g hg
  let hd := hcover.isDerivedSubgroup
  let χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
    hd.isRepresentedBy.factorHom
      (CommGroupScheme.groupHom (R.derivedCocharacter α) ≫ i) (by
        rintro U _ ⟨z, rfl⟩
        exact R.derivedCocharacter_mem α U z)
  have hχ : χ ≫ d = CommGroupScheme.groupHom (R.derivedCocharacter α) ≫ i :=
    hd.isRepresentedBy.factorHom_comp _ _
  have hpos : 0 < latticePairing S α.val (R.derivedCocharacter α) := by
    rw [R.latticePairing_derivedCocharacter α]
    norm_num
  have hgU : g ∈ (Dynamic.unipotent (χ ≫ d)).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    exact RelativeRoot.subgroup_le_dynamicUnipotent i _ hpos _ hg
  exact mem_simplyConnectedImage.mpr
    (Dynamic.exists_derivedCover_lift_of_mem_unipotent hcover χ g hgU)

end Field

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G D C : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G) {d : D ⟶ G} {π : C ⟶ D}

/-- Every sharp fixer lies in the actual simply connected image. -/
theorem sharpFixer_le_simplyConnectedImage
    (hcover : IsSimplyConnectedDerivedCover d π) (Ω : Set B.Apartment) :
    B.sharpFixer Ω ≤ simplyConnectedImage d π := by
  change (⨆ α : relativeRoots B.i, B.apartment.rootFixer α Ω) ≤ _
  refine iSup_le fun α => ?_
  exact le_trans inf_le_left
    (rootGroupPoints_le_simplyConnectedImage_of_isMaximalSplitTorus
      B.isMaximalSplitTorus hcover α)

/-- The sharp fixer of any apartment subset fixes its image pointwise. -/
theorem sharpFixer_le_pointwiseFixer (Ω : Set B.Apartment) :
    B.sharpFixer Ω ≤ B.pointwiseFixer (B.apartmentMap '' Ω) := by
  intro g hg
  apply B.apartment.mem_pointwiseFixer.mpr
  rintro _ ⟨x, hx, rfl⟩
  apply B.mem_fixer.mp
  apply B.sharpFixer_le_fixer
  exact B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hx) hg

end IntegerValuationBuildingData

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom] (E : UnramifiedZeroDatum F H)

/-- Every supplied sharp fixer over the maximal unramified field lies in the
zero subgroup computed by every supplied datum. -/
theorem sharpFixer_le_zeroPoints (B : MaximalUnramified.BuildingData F H)
    (Ω : Set B.Apartment) : B.sharpFixer Ω ≤ E.zeroPoints :=
  (B.sharpFixer_le_simplyConnectedImage E.isSimplyConnectedDerivedCover Ω).trans
    E.simplyConnectedImage_le_zeroPoints

/-- The easy inclusion in the zero/sharp comparison holds for every apartment
subset, without nonemptiness, boundedness or additional apartment axioms. -/
theorem wholeApartmentZeroFixer_sup_sharpFixer_le
    (B : MaximalUnramified.BuildingData F H) (Ω : Set B.Apartment) :
    (E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω ≤
      E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) := by
  apply sup_le
  · refine le_inf inf_le_left ?_
    intro g hg
    apply B.apartment.mem_pointwiseFixer.mpr
    intro y hy
    exact B.apartment.mem_pointwiseFixer.mp hg.2 y
      (Set.image_mono (Set.subset_univ Ω) hy)
  · exact le_inf (E.sharpFixer_le_zeroPoints B Ω) (B.sharpFixer_le_pointwiseFixer Ω)

end UnramifiedZeroDatum

end Langlands.Geometry.Building
