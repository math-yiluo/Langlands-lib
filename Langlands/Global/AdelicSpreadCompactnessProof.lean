import Langlands.Global.AdelicSpreadCompactnessStatement
import Langlands.Global.AdelicSpreadProperMapProof

/-! # Compactness of actual adelic points of proper schemes -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- The structure map to the terminal field scheme is proper on adelic points. -/
theorem curvePlaceSpreadCompactness : CurvePlaceSpreadCompactnessStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S X _ _ Y e _
  let Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))) :=
    Over.mk (𝟙 _)
  let W : Over (Spec (CommRingCat.of F)) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  let : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let : IsSeparated W.hom := by dsimp [W]; infer_instance
  let : IsIso (curvePlaceModelGenericFiber k F S Z).hom := by
    dsimp [curvePlaceModelGenericFiber, Z]
    infer_instance
  let f : curvePlaceModelGenericFiber k F S Z ≅ W :=
    Over.isoMk (asIso (curvePlaceModelGenericFiber k F S Z).hom)
  let g : Y ⟶ W := Over.homMk Y.hom
  let : IsProper g.left := by dsimp [g]; infer_instance
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceSpreadAdelePointTopology k F S Z W f
  let : Subsingleton (CurvePlaceAdelePoints k F W) :=
    ⟨fun p q => Over.mkIdTerminal.hom_ext p q⟩
  have h := curvePlaceSpreadProperMap k F S S X Z Y W e f g
  exact isCompact_univ_iff.mp (by
    simpa only [Set.preimage_univ] using h.isCompact_preimage isCompact_univ)

/-- The same argument includes every infinite completion of a number field. -/
theorem numberFieldSpreadCompactness : NumberFieldSpreadCompactnessStatement.{u} := by
  intro K _ _ S X _ _ Y e _
  let Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))) :=
    Over.mk (𝟙 _)
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  let : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let : IsSeparated W.hom := by dsimp [W]; infer_instance
  let : IsIso (numberFieldModelGenericFiber K S Z).hom := by
    dsimp [numberFieldModelGenericFiber, Z]
    infer_instance
  let f : numberFieldModelGenericFiber K S Z ≅ W :=
    Over.isoMk (asIso (numberFieldModelGenericFiber K S Z).hom)
  let g : Y ⟶ W := Over.homMk Y.hom
  let : IsProper g.left := by dsimp [g]; infer_instance
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldSpreadAdelePointTopology K S Z W f
  let : Subsingleton (NumberFieldAdelePoints K W) :=
    ⟨fun p q => Over.mkIdTerminal.hom_ext p q⟩
  have h := numberFieldSpreadProperMap K S S X Z Y W e f g
  exact isCompact_univ_iff.mp (by
    simpa only [Set.preimage_univ] using h.isCompact_preimage isCompact_univ)

/-- The compactness assertion of Conrad Proposition 4.4 in both characteristics. -/
theorem adelicSpreadCompactness : AdelicSpreadCompactnessStatement.{u} :=
  ⟨curvePlaceSpreadCompactness, numberFieldSpreadCompactness⟩

end Langlands.Global
