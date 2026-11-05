import Langlands.Global.AdelicFixedModelTransition
import Langlands.Global.AdelicSpreadSeparatedExistenceStatement
import Langlands.Global.AdelicSpreadExistenceProof
import Langlands.Global.AdelicSpreadEventualSeparationProof

/-! # Separated models over the actual arithmetic integer rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- The actual generic fiber is unchanged by enlarging the integer ring. -/
private def curvePlaceGenericFiberLevelIso
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)
    (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    curvePlaceModelGenericFiber k F T (curvePlaceLevelModelBaseChange k F hST M) ≅
      curvePlaceModelGenericFiber k F S M :=
  Langlands.AlgebraicGeometry.PointTopology.modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F T).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) M

/-- The corresponding comparison uses the literal number-field inclusions. -/
private def numberFieldGenericFiberLevelIso
    (K : Type u) [Field K] [NumberField K]
    {S T : Finset (FinitePlace K)} (hST : S ⊆ T)
    (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    numberFieldModelGenericFiber K T (numberFieldLevelModelBaseChange K hST M) ≅
      numberFieldModelGenericFiber K S M :=
  Langlands.AlgebraicGeometry.PointTopology.modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST)))
    (Spec.map (CommRingCat.ofHom ((T : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) M

/-- Descend a finite-type scheme, then enlarge its integer base until
the supplied separated generic fiber gives a separated model. -/
theorem curvePlaceSpreadSeparatedExistence :
    CurvePlaceSpreadSeparatedExistenceStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S Y _ _ _
  obtain ⟨T, M, hft, hqc, ⟨e⟩⟩ := curvePlaceSpreadExistence k F S Y
  let : LocallyOfFiniteType M.hom := hft
  let : QuasiCompact M.hom := hqc
  have hsep : IsSeparated (curvePlaceModelGenericFiber k F T.val M).hom := by
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨U, hU⟩ :=
    (curvePlaceSpreadEventualSeparation k F T.val M).mp hsep
  let N := curvePlaceLevelModelBaseChange k F U.property M
  refine ⟨⟨U.val, T.property.trans U.property⟩, N, ?_, ?_, hU,
    ⟨curvePlaceGenericFiberLevelIso k F U.property M ≪≫ e⟩⟩
  · dsimp [N, curvePlaceLevelModelBaseChange]
    infer_instance
  · dsimp [N, curvePlaceLevelModelBaseChange]
    infer_instance

/-- The same construction retains the original number field and all
finite initial place sets. -/
theorem numberFieldSpreadSeparatedExistence :
    NumberFieldSpreadSeparatedExistenceStatement.{u} := by
  intro K _ _ S Y _ _ _
  obtain ⟨T, M, hft, hqc, ⟨e⟩⟩ := numberFieldSpreadExistence K S Y
  let : LocallyOfFiniteType M.hom := hft
  let : QuasiCompact M.hom := hqc
  have hsep : IsSeparated (numberFieldModelGenericFiber K T.val M).hom := by
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨U, hU⟩ :=
    (numberFieldSpreadEventualSeparation K T.val M).mp hsep
  let N := numberFieldLevelModelBaseChange K U.property M
  refine ⟨⟨U.val, T.property.trans U.property⟩, N, ?_, ?_, hU,
    ⟨numberFieldGenericFiberLevelIso K U.property M ≪≫ e⟩⟩
  · dsimp [N, numberFieldLevelModelBaseChange]
    infer_instance
  · dsimp [N, numberFieldLevelModelBaseChange]
    infer_instance

/-- Separated finite-type schemes have separated actual arithmetic spreads. -/
theorem adelicSpreadSeparatedExistence :
    AdelicSpreadSeparatedExistenceStatement.{u} :=
  ⟨curvePlaceSpreadSeparatedExistence, numberFieldSpreadSeparatedExistence⟩

end Langlands.Global
