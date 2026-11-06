import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionIntersections
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRelativeProduct
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionClosedImmersionProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The actual diagonal chart map from the Weil restriction of an original
affine intersection to the relative product of the two Weil charts. -/
def affineChartWeilRestrictionDiagonalChartMap
    (U V : Y.left.affineOpens) (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    (affineWeilRestriction A B (openOver B Y (U.val ⊓ V.val))).left ⟶
      pullback (affineWeilRestriction A B (openOver B Y U.val)).hom
        (affineWeilRestriction A B (openOver B Y V.val)).hom := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  exact pullback.lift
    (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val))).left
    (affineWeilRestrictionMap A B
      (openOverHomOfLE B Y (inf_le_right : U.val ⊓ V.val ≤ V.val))).left
    ((Over.w _).trans (Over.w _).symm)

/-- The original separated diagonal supplies a closed immersion on each
actual affine Weil chart pair. -/
theorem affineChartWeilRestrictionDiagonalChartMap_isClosedImmersion
    [IsSeparated Y.hom] (U V : Y.left.affineOpens)
    (hUV : IsAffineOpen (U.val ⊓ V.val)) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    IsClosedImmersion (affineChartWeilRestrictionDiagonalChartMap A B Y U V hUV) := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  let X := openOver B Y U.val
  let Z := openOver B Y V.val
  let P := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)
  let : IsAffine P.left := inferInstanceAs (IsAffine (pullback X.hom Z.hom))
  let : LocallyOfFiniteType P.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Z.hom ≫ X.hom))
  let f : openOver B Y (U.val ⊓ V.val) ⟶ P := Over.homMk
    ((isPullback_opens_inf U.val V.val).isoPullback.hom ≫
      pullback.mapDesc U.val.ι V.val.ι Y.hom) (by
        dsimp [P, X, Z, openOver]
        simp only [Category.assoc, pullback.lift_fst_assoc, Category.comp_id,
          IsPullback.isoPullback_hom_fst_assoc]
        exact Y.left.homOfLE_ι_assoc _ _)
  let p₁ : P ⟶ X := Over.homMk (pullback.fst X.hom Z.hom) rfl
  let p₂ : P ⟶ Z := Over.homMk (pullback.snd X.hom Z.hom) pullback.condition.symm
  have hf₁ : f ≫ p₁ = openOverHomOfLE B Y
      (inf_le_left : U.val ⊓ V.val ≤ U.val) := by
    apply Over.OverMorphism.ext
    change ((isPullback_opens_inf U.val V.val).isoPullback.hom ≫
      pullback.mapDesc U.val.ι V.val.ι Y.hom) ≫
        pullback.fst (U.val.ι ≫ Y.hom) (V.val.ι ≫ Y.hom) =
      Y.left.homOfLE inf_le_left
    simp only [Category.assoc, pullback.lift_fst, Category.comp_id,
      IsPullback.isoPullback_hom_fst]
  have hf₂ : f ≫ p₂ = openOverHomOfLE B Y
      (inf_le_right : U.val ⊓ V.val ≤ V.val) := by
    apply Over.OverMorphism.ext
    change ((isPullback_opens_inf U.val V.val).isoPullback.hom ≫
      pullback.mapDesc U.val.ι V.val.ι Y.hom) ≫
        pullback.snd (U.val.ι ≫ Y.hom) (V.val.ι ≫ Y.hom) =
      Y.left.homOfLE inf_le_right
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id,
      IsPullback.isoPullback_hom_snd]
  let : IsClosedImmersion f.left := by
    change IsClosedImmersion
      ((isPullback_opens_inf U.val V.val).isoPullback.hom ≫
        pullback.mapDesc U.val.ι V.val.ι Y.hom)
    infer_instance
  let : IsClosedImmersion (affineWeilRestrictionMap A B f).left :=
    affineWeilRestrictionMap_isClosedImmersion A B f
  have he : affineChartWeilRestrictionDiagonalChartMap A B Y U V hUV =
      (affineWeilRestrictionMap A B f).left ≫
        (affineWeilRestrictionRelativeProductIso A B X Z).hom := by
    apply pullback.hom_ext
    · dsimp only [affineChartWeilRestrictionDiagonalChartMap]
      rw [pullback.lift_fst, Category.assoc,
        affineWeilRestrictionRelativeProductIso_hom_fst]
      change (affineWeilRestrictionMap A B _).left =
        (affineWeilRestrictionMap A B f ≫ affineWeilRestrictionMap A B p₁).left
      rw [← affineWeilRestrictionMap_comp, hf₁]
    · dsimp only [affineChartWeilRestrictionDiagonalChartMap]
      rw [pullback.lift_snd, Category.assoc,
        affineWeilRestrictionRelativeProductIso_hom_snd]
      change (affineWeilRestrictionMap A B _).left =
        (affineWeilRestrictionMap A B f ≫ affineWeilRestrictionMap A B p₂).left
      rw [← affineWeilRestrictionMap_comp, hf₂]
  rw [he]
  infer_instance

/-- The actual chart-overlap map into the relative product is closed. -/
theorem affineChartWeilRestriction_mapDesc_isClosedImmersion
    [IsSeparated Y.hom] (U V : Y.left.affineOpens) :
    IsClosedImmersion (pullback.mapDesc
      (affineChartWeilRestrictionι A B Y U).left
      (affineChartWeilRestrictionι A B Y V).left
      (affineChartWeilRestriction A B Y).hom) := by
  let : Y.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.hom]
    infer_instance⟩
  have hUV : IsAffineOpen (U.val ⊓ V.val) := U.property.inf V.property
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  let h := (affineChartWeilRestrictionIntersection_isPullback A B Y U V hUV).map
    (Over.forget (Spec (CommRingCat.of A)))
  let : IsClosedImmersion (affineChartWeilRestrictionDiagonalChartMap A B Y U V hUV) :=
    affineChartWeilRestrictionDiagonalChartMap_isClosedImmersion A B Y U V hUV
  let e := pullback.congrHom
    (Over.w (affineChartWeilRestrictionι A B Y U))
    (Over.w (affineChartWeilRestrictionι A B Y V))
  have he : h.isoPullback.inv ≫ affineChartWeilRestrictionDiagonalChartMap A B Y U V hUV =
      pullback.mapDesc (affineChartWeilRestrictionι A B Y U).left
        (affineChartWeilRestrictionι A B Y V).left
        (affineChartWeilRestriction A B Y).hom ≫ e.hom := by
    apply pullback.hom_ext
    · dsimp only [affineChartWeilRestrictionDiagonalChartMap]
      simp only [e, pullback.congrHom_hom, Category.assoc, pullback.lift_fst,
        Category.comp_id]
      exact h.isoPullback_inv_fst
    · dsimp only [affineChartWeilRestrictionDiagonalChartMap]
      simp only [e, pullback.congrHom_hom, Category.assoc, pullback.lift_snd,
        Category.comp_id]
      exact h.isoPullback_inv_snd
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ e.hom]
  rw [← he]
  infer_instance

/-- The existing glued Weil model has a closed diagonal when the original
target is separated. -/
instance affineChartWeilRestriction_isSeparated [IsSeparated Y.hom] :
    IsSeparated (affineChartWeilRestriction A B Y).hom := by
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  apply (HasAffineProperty.diagonal_iff (P := @IsClosedImmersion)).mp
  let := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  let 𝒰 := affineChartWeilRestrictionOpenCover A B Y
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    inferInstanceAs (IsAffine (affineWeilRestriction A B (openOver B Y i.val)).left)
  apply AffineTargetMorphismProperty.diagonal_of_openCover_source
    (Q := fun X _ f => IsAffine X ∧ Function.Surjective f.appTop)
    (affineChartWeilRestriction A B Y).hom 𝒰
  intro U V
  apply (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp
  exact affineChartWeilRestriction_mapDesc_isClosedImmersion A B Y U V

end Langlands.AlgebraicGeometry.PointTopology
