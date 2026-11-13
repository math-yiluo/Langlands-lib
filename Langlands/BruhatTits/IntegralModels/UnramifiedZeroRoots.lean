import Langlands.Geometry.Building.KPSharpCoverImageProof
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRoots

/-! # Actual derived-cover lifts and root intersections of unramified zero fixers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section Field

variable {k : Type u} [Field k]
    {G D H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (d : D ⟶ G) (π : H ⟶ D) (hcover : IsSimplyConnectedDerivedCover d π)

include hi hcover in
/-- Every actual relative-root point lifts through any supplied simply
connected derived cover, over an arbitrary field. -/
theorem exists_rootPoint_derivedCoverLift (a : relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) :
    ∃ h : rationalPoints H, rationalPoints.map (π ≫ d) h = g := by
  let : Mono i.hom.hom.left := mono_of_isMaximalSplitTorus hi
  obtain ⟨W, _⟩ := relativeRootReflectionExistence_of_rootRankOneFactorization
    rootRankOneFactorization k G hcover.isConnectedReductive S i hi
  let hd := hcover.isDerivedSubgroup
  let χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
    hd.isRepresentedBy.factorHom
      (CommGroupScheme.groupHom (W.derivedCocharacter a) ≫ i) (by
        rintro U _ ⟨z, rfl⟩
        exact W.derivedCocharacter_mem a U z)
  have hχ : χ ≫ d = CommGroupScheme.groupHom (W.derivedCocharacter a) ≫ i :=
    hd.isRepresentedBy.factorHom_comp _ _
  have hpos : 0 < latticePairing S a.val (W.derivedCocharacter a) := by
    rw [W.latticePairing_derivedCocharacter a]
    norm_num
  have hgU : g ∈ (Dynamic.unipotent (χ ≫ d)).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    exact RelativeRoot.subgroup_le_dynamicUnipotent i _ hpos _ hg
  exact Dynamic.exists_derivedCover_lift_of_mem_unipotent hcover χ g hgU

/-- A chosen actual cover point above the specified actual relative-root
point. The construction does not use any valuation or apartment axiom. -/
def rootPointDerivedCoverLift (a : relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) : rationalPoints H :=
  Classical.choose (exists_rootPoint_derivedCoverLift i hi d π hcover a g hg)

@[simp]
theorem rootPointDerivedCoverLift_map (a : relativeRoots i)
    (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) :
    rationalPoints.map (π ≫ d) (rootPointDerivedCoverLift i hi d π hcover a g hg) = g :=
  Classical.choose_spec (exists_rootPoint_derivedCoverLift i hi d π hcover a g hg)

end Field

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

/-- Every root group for C's apartment is in the simply connected image of
any zero datum E, independently of E's chosen maximal torus. -/
theorem unramifiedRootGroup_le_simplyConnectedImage (a : relativeRoots C.i) :
    rootGroupPoints C.i a ≤ E.simplyConnectedImage := by
  intro g hg
  exact mem_simplyConnectedImage.mpr
    (exists_rootPoint_derivedCoverLift C.i C.isMaximalSplitTorus
      E.d E.π E.isSimplyConnectedDerivedCover a g hg)

/-- The sharp fixer of every apartment subset lies in the zero subgroup of
any supplied zero datum, without a compatibility condition on its torus. -/
theorem unramifiedSharpFixer_le_zeroPoints (Ω : Set C.Apartment) :
    C.sharpFixer Ω ≤ E.zeroPoints := by
  apply iSup_le
  intro a
  exact (inf_le_left.trans (unramifiedRootGroup_le_simplyConnectedImage C E a)).trans
    E.simplyConnectedImage_le_zeroPoints

/-- The actual zero-fixer/root intersection is the actual root fixer for
any zero datum, with no extra apartment axioms or topology on the upper field. -/
theorem rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer
    (Ω : Set C.Apartment) (a : relativeRoots C.i) :
    rootGroupPoints C.i a ⊓ (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) =
      C.apartment.rootFixer a Ω := by
  rw [← inf_assoc, inf_eq_left.mpr
    ((unramifiedRootGroup_le_simplyConnectedImage C E a).trans
      E.simplyConnectedImage_le_zeroPoints)]
  exact C.apartment.rootGroupPoints_inf_pointwiseFixer_eq_rootFixer
    C.isConnectedReductive C.isMaximalSplitTorus a Ω

/-- From a supplied full fixer model, the neutral-model and arbitrary
zero-fixer intersections agree on every actual relative root group. -/
theorem rootGroupPoints_inf_unramifiedNeutral_eq_zeroFixer
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (a : relativeRoots C.i) :
    rootGroupPoints C.i a ⊓ D.neutral.integralPoints =
      rootGroupPoints C.i a ⊓ (E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) := by
  rw [rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C D Ω hN a,
    rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω a]

end Unramified

end Langlands.BruhatTits.IntegralModels
