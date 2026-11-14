import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageProof
import Langlands.GroupScheme.SimplyConnected.CommutativeDerivedCoverConstruction
import Langlands.GroupScheme.Torus.ConnectedReductive

/-! # Unramified zero points in a compatible torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G)

/-- Zero data for the specified torus itself, with its original splitting
field and the actual trivial simply connected derived cover. -/
def torusZeroDatum : UnramifiedZeroDatum F E.T.toGrp := by
  classical
  have hT := E.isMaximallySplitMaximalTorus.1.1
  have hred : IsConnectedReductive E.T.toGrp := hT.isConnectedReductive_of_fieldSplitting
  let : IsAffineHom E.T.toGrp.X.hom := hred.isAffineHom
  let : Smooth E.T.toGrp.X.hom := hred.smooth
  let hA := exists_maximalSplitTorus E.T.toGrp
  let A := hA.choose
  let a := hA.choose_spec.choose
  have ha := hA.choose_spec.choose_spec
  let cov := commutativeDerivedCoverData E.T.toGrp hred
  exact {
    T := E.T
    i := 𝟙 E.T.toGrp
    isMaximallySplitMaximalTorus := ⟨
      IsMaximalTorus.of_comp E.isMaximallySplitMaximalTorus.1.2.1
        (by simpa only [Category.id_comp] using E.isMaximallySplitMaximalTorus.1),
      A, a, a, ha, Category.comp_id a⟩
    L := E.L
    isSplitTorus := E.isSplitTorus
    D := Grp.trivial (Over (Spec (CommRingCat.of (UnramifiedClosure F))))
    C := Grp.trivial (Over (Spec (CommRingCat.of (UnramifiedClosure F))))
    d := cov.val
    π := 𝟙 _
    isSimplyConnectedDerivedCover := cov.property }

@[simp]
theorem torusZeroDatum_torusIwahori : E.torusZeroDatum.torusIwahori = E.torusIwahori := rfl

/-- The zero points of the torus datum are exactly the original norm-defined
Iwahori subgroup. -/
theorem torusZeroDatum_zeroPoints : E.torusZeroDatum.zeroPoints = E.torusIwahori := by
  have hcover : E.torusZeroDatum.simplyConnectedImage = ⊥ := by
    apply le_antisymm _ bot_le
    rintro t ⟨c, rfl⟩
    change rationalPoints.map (𝟙 _ ≫ kernelUnit E.T.toGrp) c = 1
    have hc : c = 1 := toUnit_unique _ _
    rw [hc, map_one]
  rw [zeroPoints, hcover, bot_sup_eq]
  change E.torusIwahori.map (rationalPoints.map (𝟙 E.T.toGrp)) = _
  have hid : rationalPoints.map (𝟙 E.T.toGrp) = MonoidHom.id _ := by
    ext t
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id, MonoidHom.id_apply]
  rw [hid, Subgroup.map_id]

/-- Norm-defined Iwahori points have unit values under every rational
character for the prescribed fixed-field valuation. -/
theorem torusIwahori_le_fixedField_characterValuationKernel :
    E.torusIwahori ≤ characterValuationKernel (fixedFieldValuation F) E.T.toGrp :=
  torusNormIwahori_le_characterValuationKernel (fixedFieldValuation F)
    (intermediateValuation F E.L) (intermediateValuation_conjugate F E.L) E.T

/-- The cover image in a split-torus centralizer, intersected with its
character-valuation kernel, lies in the centralizer's unramified zero points. -/
theorem coverImage_comap_inf_characterValuationKernel_le_zeroPoints
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    {a : A.toGrp ⟶ G} (ha : IsSplitSubtorus a)
    (hE : (torusCentralizer a).IsRepresentedBy E.i) :
    E.simplyConnectedImage.comap (rationalPoints.map E.i) ⊓
        characterValuationKernel (fixedFieldValuation F) E.T.toGrp ≤ E.torusIwahori := by
  have h := coverImage_inf_characterValuationKernel_le_zeroPoints
    cocenterQuotientExistence splitTorusCentralizerCocenterInduced inducedTorusIwahori
    splitTorusCentralizerCoverPreimage E.isSimplyConnectedDerivedCover.isConnectedReductive
    E.isSimplyConnectedDerivedCover.isDerivedSubgroup
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny ha hE E.torusZeroDatum
  rw [E.torusZeroDatum_zeroPoints] at h
  exact h

/-- At the original torus inclusion, the ambient zero points intersected
with the torus character-valuation kernel are exactly the torus Iwahori points. -/
theorem zeroPoints_comap_inf_characterValuationKernel_eq_torusIwahori
    {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    {a : A.toGrp ⟶ G} (ha : IsSplitSubtorus a)
    (hE : (torusCentralizer a).IsRepresentedBy E.i) :
    E.zeroPoints.comap (rationalPoints.map E.i) ⊓
        characterValuationKernel (fixedFieldValuation F) E.T.toGrp = E.torusIwahori := by
  apply le_antisymm
  · rintro t ⟨htG, htK⟩
    obtain ⟨c, hc, s, hs, heq⟩ := E.mem_zeroPoints_iff.mp htG
    have hdiff : rationalPoints.map E.i (t * s⁻¹) = c := by
      rw [map_mul, map_inv, ← heq, mul_inv_cancel_right]
    have hcover : t * s⁻¹ ∈ E.simplyConnectedImage.comap (rationalPoints.map E.i) := by
      change rationalPoints.map E.i (t * s⁻¹) ∈ E.simplyConnectedImage
      rw [hdiff]
      exact hc
    have hkernel : t * s⁻¹ ∈ characterValuationKernel (fixedFieldValuation F) E.T.toGrp :=
      Subgroup.mul_mem _ htK (Subgroup.inv_mem _
        (E.torusIwahori_le_fixedField_characterValuationKernel hs))
    have hzero := E.coverImage_comap_inf_characterValuationKernel_le_zeroPoints ha hE
      ⟨hcover, hkernel⟩
    simpa only [inv_mul_cancel_right] using E.torusIwahori.mul_mem hzero hs
  · intro t ht
    exact ⟨E.map_torusIwahori_le_zeroPoints ⟨t, ht, rfl⟩,
      E.torusIwahori_le_fixedField_characterValuationKernel ht⟩

end Langlands.Geometry.Building.UnramifiedZeroDatum
