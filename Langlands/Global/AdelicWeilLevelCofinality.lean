import Langlands.Global.NumberFieldSIntegerFixedLevelRegroup
import Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelRegroup
import Langlands.Global.AdelicFixedModelCocone
import Langlands.Global.AdelicFixedModelTransitionTopologyProof
import Mathlib.CategoryTheory.Filtered.Final

noncomputable section

universe u v

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped NumberField AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.NumberFieldSIntegers

namespace Langlands.Global.AdelicWeilLevelCofinality

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section NumberField

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- Full upper preimages preserve inclusion of enlarged lower supports. -/
theorem numberFieldUpperLevel_mono :
    Monotone (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S) := by
  intro T U hTU q hq
  exact (mem_numberFieldExceptionalPreimage U.val q).mpr
    (hTU ((mem_numberFieldExceptionalPreimage T.val q).mp hq))

/-- The actual full-preimage functor on supports above the original bases. -/
def numberFieldUpperLevelFunctor :
    AdelicLevelIndexAbove S ⥤
      AdelicLevelIndexAbove (numberFieldExceptionalPreimage (L := L) S) :=
  (numberFieldUpperLevel_mono K L S).functor

/-- Enlarge below by the restrictions of a prescribed finite upper support. -/
def numberFieldLevelCover
    (U : AdelicLevelIndexAbove (numberFieldExceptionalPreimage (L := L) S)) :
    AdelicLevelIndexAbove S := by
  classical
  exact ⟨S ∪ U.val.image (HeightOneSpectrum.under (NumberField.RingOfIntegers K)),
    Finset.subset_union_left⟩

/-- The full upper preimage of this concrete lower enlargement contains the prescribed support. -/
theorem numberFieldLevelCover_spec
    (U : AdelicLevelIndexAbove (numberFieldExceptionalPreimage (L := L) S)) :
    U ≤ NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S
      (numberFieldLevelCover K L S U) :=
  numberField_subset_exceptionalPreimage_union_image S U.val

/-- Full upper preimages form a final family among all enlarged upper supports. -/
instance numberFieldUpperLevelFunctor_final :
    (numberFieldUpperLevelFunctor K L S).Final := by
  let := IsFiltered.isDirectedOrder (AdelicLevelIndexAbove S)
  exact (numberFieldUpperLevel_mono K L S).final_functor_iff.mpr fun U =>
    ⟨numberFieldLevelCover K L S U, numberFieldLevelCover_spec K L S U⟩

variable (Y : Over (Spec (CommRingCat.of
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L))))
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- Continuity out of actual upper adelic points is detected on full-preimage levels alone. -/
theorem numberField_continuous_iff {Z : Type v} [TopologicalSpace Z]
    (f : NumberFieldFixedModelAdelePoints L
      (numberFieldExceptionalPreimage (L := L) S) Y → Z) :
    Continuous[numberFieldFixedModelAdelePointTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y, inferInstance] f ↔
      ∀ T : AdelicLevelIndexAbove S,
        Continuous[numberFieldFixedModelStageTopology L
          (numberFieldExceptionalPreimage (L := L) S) Y
          (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T), inferInstance]
          (f ∘ fun p => p.changeRing
            (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S)
              (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T)).hom) := by
  refine (ringPointCoconeTopology_continuous_iff
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)
    (numberFieldAdeleLevelOverDiagram L (numberFieldExceptionalPreimage (L := L) S)) Y
    (numberFieldFixedModelStageTopology L (numberFieldExceptionalPreimage (L := L) S) Y)
    (numberFieldAdeleOverCocone L (numberFieldExceptionalPreimage (L := L) S)) f).trans ?_
  constructor
  · intro h T
    exact h _
  · intro h U
    let T := numberFieldLevelCover K L S U
    let V := NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T
    have hUV : U ≤ V := numberFieldLevelCover_spec K L S U
    let := numberFieldFixedModelStageTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y U
    let := numberFieldFixedModelStageTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y V
    change Continuous[numberFieldFixedModelStageTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y U, inferInstance]
      (f ∘ fun p : RingPoint
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) Y
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) U) =>
          p.changeRing
            (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S) U).hom)
    have hc := (numberFieldFixedModelTransitionTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y U V hUV).1
    have hh := (h T).comp hc
    convert hh using 1
    funext p
    dsimp only [Function.comp_def]
    apply congrArg f
    apply RingPoint.ext
    change Spec.map _ ≫ p.left = Spec.map _ ≫ (Spec.map _ ≫ p.left)
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end NumberField

section Curve

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Full upper preimages preserve inclusion above the original principal support. -/
theorem curveUpperLevel_mono :
    Monotone (CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t) := by
  intro T U hTU q hq
  exact (mem_curvePlaceExceptionalPreimage U.val q).mpr
    (hTU ((mem_curvePlaceExceptionalPreimage T.val q).mp hq))

/-- The actual full-preimage functor above the fixed principal integral bases. -/
def curveUpperLevelFunctor :
    AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)) ⥤
      AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))) :=
  (curveUpperLevel_mono k K L s t).functor

/-- Enlarge below by the actual restrictions of every prescribed upper place. -/
def curveLevelCover
    (U : AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) :
    AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)) := by
  classical
  exact ⟨curvePlacePrincipalExceptional k K s (t : K) ∪ U.val.image curvePlaceRestriction,
    Finset.subset_union_left⟩

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The concrete lower enlargement covers the whole prescribed upper support. -/
theorem curveLevelCover_spec
    (U : AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) :
    U ≤ CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t
      (curveLevelCover k K L s t U) :=
  curvePlace_subset_exceptionalPreimage_union_image
    (curvePlacePrincipalExceptional k K s (t : K)) U.val

/-- Full upper preimages form a final family among all enlarged upper curve supports. -/
instance curveUpperLevelFunctor_final :
    (curveUpperLevelFunctor k K L s t).Final := by
  let := IsFiltered.isDirectedOrder
    (AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))
  exact (curveUpperLevel_mono k K L s t).final_functor_iff.mpr fun U =>
    ⟨curveLevelCover k K L s t U, curveLevelCover_spec k K L s t U⟩

variable (Y : Over (Spec (CommRingCat.of
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The actual upper adelic topology is detected on full-preimage enlargements of the fixed base. -/
theorem curve_continuous_iff {Z : Type v} [TopologicalSpace Z]
    (f : CurvePlaceFixedModelAdelePoints k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y → Z) :
    Continuous[curvePlaceFixedModelAdelePointTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y,
      inferInstance] f ↔
      ∀ T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)),
        Continuous[curvePlaceFixedModelStageTopology k L
          (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y
          (CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t T), inferInstance]
          (f ∘ fun p => p.changeRing
            (curvePlaceAdeleLevelOverι k L
              (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
              (CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t T)).hom) := by
  let : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
  let : IsScalarTower (RatFunc k) K L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (RatFunc k) L := .of_algebraMap_eq fun a => by
    change algebraMap k L a =
      algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
    rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
      ← IsScalarTower.algebraMap_apply k K L]
  let : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
  refine (ringPointCoconeTopology_continuous_iff
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceAdeleLevelOverDiagram k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
    (curvePlaceFixedModelStageTopology k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))) Y)
    (curvePlaceAdeleOverCocone k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) f).trans ?_
  constructor
  · intro h T
    exact h _
  · intro h U
    let T := curveLevelCover k K L s t U
    let V := CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t T
    have hUV : U ≤ V := curveLevelCover_spec k K L s t U
    let := curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y U
    let := curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y V
    change Continuous[curvePlaceFixedModelStageTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y U,
      inferInstance]
      (f ∘ fun p : RingPoint
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (curvePlaceAdeleLevelOver k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))) U) =>
          p.changeRing (curvePlaceAdeleLevelOverι k L
            (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) U).hom)
    have hc := (curvePlaceFixedModelTransitionTopology k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      Y U V hUV).1
    have hh := (h T).comp hc
    convert hh using 1
    funext p
    dsimp only [Function.comp_def]
    apply congrArg f
    apply RingPoint.ext
    change Spec.map _ ≫ p.left = Spec.map _ ≫ (Spec.map _ ≫ p.left)
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end Curve

end Langlands.Global.AdelicWeilLevelCofinality
