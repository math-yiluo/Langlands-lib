import Langlands.Global.AdelicFixedModelSystem

/-! # Coherent changes of arithmetic level over the original model base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false in
/-- Compare an iterated actual model pullback with its direct pullback. -/
def modelPullbackCompIso {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (h : T ⟶ R) (w : g ≫ f = h)
    (X : Over R) :
    (Over.pullback g).obj ((Over.pullback f).obj X) ≅ (Over.pullback h).obj X :=
  Over.isoMk ((pullbackLeftPullbackSndIso X.hom f g) ≪≫
    pullback.congrHom rfl w) (by simp [pullback.map])

set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves the composite projection to the original model. -/
@[simp, reassoc]
theorem modelPullbackCompIso_hom_left_fst {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (h : T ⟶ R) (w : g ≫ f = h)
    (X : Over R) :
    (modelPullbackCompIso f g h w X).hom.left ≫ pullback.fst X.hom h =
      pullback.fst ((Over.pullback f).obj X).hom g ≫ pullback.fst X.hom f := by
  simp [modelPullbackCompIso, pullback.map]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The canonical comparison from the twice-pulled model to the direct model. -/
def curvePlaceFixedModelPullbackCompIso {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    curvePlaceLevelModelBaseChange k F hTU
        (curvePlaceLevelModelBaseChange k F T.property X) ≅
      curvePlaceLevelModelBaseChange k F U.property X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hTU)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F U.property)))
    (by rw [← Spec.map_comp]; rfl) X

/-- Fixed-base coefficient change agrees with the original changing-model map. -/
theorem curvePlaceFixedModelTransition_natural {T U : AdelicLevelIndexAbove S}
    (hTU : T ≤ U)
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    (curvePlaceFixedModelPointEquiv k F S X U).symm
        (curvePlaceLevelModelTransition k F hTU
            (curvePlaceLevelModelBaseChange k F T.property X)
            (curvePlaceFixedModelPointEquiv k F S X T p) ≫
          (curvePlaceFixedModelPullbackCompIso k F S X hTU).hom) =
      p.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom := by
  apply RingPoint.ext
  erw [curvePlaceFixedModelPointEquiv_symm_left]
  change (_ ≫ _) ≫ _ = _
  erw [Category.assoc]
  erw [modelPullbackCompIso_hom_left_fst]
  erw [← Category.assoc]
  erw [curvePlaceLevelModelTransition_left_fst k F hTU
    (curvePlaceLevelModelBaseChange k F T.property X)
    (curvePlaceFixedModelPointEquiv k F S X T p)]
  erw [Category.assoc]
  have hproj :
      (curvePlaceFixedModelPointEquiv k F S X T p).left ≫
          pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property))) =
        p.left := by
    exact (curvePlaceFixedModelPointEquiv_symm_left k F S X T _).symm.trans
      (congrArg (fun q => q.left)
        ((curvePlaceFixedModelPointEquiv k F S X T).symm_apply_apply p))
  erw [hproj]
  rfl

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The canonical comparison from the twice-pulled number-field model to the direct model. -/
def numberFieldFixedModelPullbackCompIso {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    numberFieldLevelModelBaseChange K hTU
        (numberFieldLevelModelBaseChange K T.property X) ≅
      numberFieldLevelModelBaseChange K U.property X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hTU)))
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K U.property)))
    (by rw [← Spec.map_comp]; rfl) X

/-- Full number-field coefficient change agrees with the original changing-model map. -/
theorem numberFieldFixedModelTransition_natural {T U : AdelicLevelIndexAbove S}
    (hTU : T ≤ U)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    (numberFieldFixedModelPointEquiv K S X U).symm
        (numberFieldLevelModelTransition K hTU
            (numberFieldLevelModelBaseChange K T.property X)
            (numberFieldFixedModelPointEquiv K S X T p) ≫
          (numberFieldFixedModelPullbackCompIso K S X hTU).hom) =
      p.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom := by
  apply RingPoint.ext
  erw [numberFieldFixedModelPointEquiv_symm_left]
  change (_ ≫ _) ≫ _ = _
  erw [Category.assoc]
  erw [modelPullbackCompIso_hom_left_fst]
  erw [← Category.assoc]
  erw [numberFieldLevelModelTransition_left_fst K hTU
    (numberFieldLevelModelBaseChange K T.property X)
    (numberFieldFixedModelPointEquiv K S X T p)]
  erw [Category.assoc]
  have hproj :
      (numberFieldFixedModelPointEquiv K S X T p).left ≫
          pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property))) =
        p.left := by
    exact (numberFieldFixedModelPointEquiv_symm_left K S X T _).symm.trans
      (congrArg (fun q => q.left)
        ((numberFieldFixedModelPointEquiv K S X T).symm_apply_apply p))
  erw [hproj]
  rfl

end NumberField

end Langlands.Global
