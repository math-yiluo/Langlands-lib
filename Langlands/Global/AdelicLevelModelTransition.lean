import Langlands.Global.AdelicLevelModelTopology
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Actual changes of level for adelic model points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)

/-- The literal inclusion of the actual outside-`S` integers in the outside-`T` integers. -/
def curvePlaceSIntegersMap :
    curvePlaceSIntegers k F S →+* curvePlaceSIntegers k F T :=
  Subring.inclusion (curvePlaceSIntegers_mono k F hST)

@[simp]
theorem curvePlaceSIntegersMap_coe (c : curvePlaceSIntegers k F S) :
    (curvePlaceSIntegersMap k F hST c : F) = c := rfl

/-- The original integer diagonals commute with the literal level inclusions. -/
theorem curvePlaceAdeleLevelDiagonal_natural :
    (curvePlaceAdeleLevelMap k F hST).comp (curvePlaceAdeleLevelDiagonal k F S) =
      (curvePlaceAdeleLevelDiagonal k F T).comp (curvePlaceSIntegersMap k F hST) := by
  ext c
  rfl

/-- The actual pullback of a model along the inclusion of its S-integer base. -/
def curvePlaceLevelModelBaseChange
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST)))).obj X

/-- Change the actual level ring and lift the resulting point to the actual pulled-back model. -/
def curvePlaceLevelModelTransition
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) →
      RingPoint (curvePlaceSIntegers k F T) (curvePlaceLevelModelBaseChange k F hST X)
        (curvePlaceAdeleLevel k F T) := fun p =>
  Over.homMk
    (pullback.lift
      (Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST)) ≫ p.left)
      (Spec.algebraMap (curvePlaceSIntegers k F T) (curvePlaceAdeleLevel k F T))
      (by
        have hp : p.left ≫ X.hom = Spec.algebraMap _ _ := Over.w p
        change (Spec.map _ ≫ p.left) ≫ X.hom = _
        erw [Category.assoc, hp]
        change Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST)) ≫
            Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelDiagonal k F S)) =
          Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelDiagonal k F T)) ≫
            Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
          (curvePlaceAdeleLevelDiagonal_natural k F hST)))
    (by
      change _ ≫ pullback.snd _ _ = Spec.algebraMap _ _
      exact pullback.lift_snd _ _ _)

/-- The transition projects to coefficient restriction of the original point. -/
@[simp]
theorem curvePlaceLevelModelTransition_left_fst
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) :
    (curvePlaceLevelModelTransition k F hST X p).left ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))) =
        Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST)) ≫ p.left := by
  exact pullback.lift_fst _ _ _

/-- The transition retains the original T-integer structure map of its test spectrum. -/
@[simp]
theorem curvePlaceLevelModelTransition_left_snd
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) :
    (curvePlaceLevelModelTransition k F hST X p).left ≫
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))) =
        Spec.algebraMap (curvePlaceSIntegers k F T) (curvePlaceAdeleLevel k F T) := by
  exact pullback.lift_snd _ _ _

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable {S T : Finset (FinitePlace K)} (hST : S ⊆ T)

/-- The literal inclusion of Mathlib's original number-field S-integer rings. -/
def numberFieldSIntegersMap :
    (S : Set (FinitePlace K)).integer K →+* (T : Set (FinitePlace K)).integer K :=
  Subring.inclusion (fun _ hc v hv => hc v (fun h => hv (hST h)))

@[simp]
theorem numberFieldSIntegersMap_coe (c : (S : Set (FinitePlace K)).integer K) :
    (numberFieldSIntegersMap K hST c : K) = c := rfl

/-- The full number-field integer diagonals commute with the original level inclusions. -/
theorem numberFieldAdeleLevelDiagonal_natural :
    (numberFieldAdeleLevelMap K hST).comp (numberFieldAdeleLevelDiagonal K S) =
      (numberFieldAdeleLevelDiagonal K T).comp (numberFieldSIntegersMap K hST) := by
  ext c
  rfl

/-- The actual pullback of a number-field model along the inclusion of S-integer rings. -/
def numberFieldLevelModelBaseChange
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    Over (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST)))).obj X

/-- The actual full-level transition into points of the pulled-back model, including all infinite places. -/
def numberFieldLevelModelTransition
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) →
      RingPoint ((T : Set (FinitePlace K)).integer K) (numberFieldLevelModelBaseChange K hST X)
        (numberFieldAdeleLevel K T) := fun p =>
  Over.homMk
    (pullback.lift
      (Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST)) ≫ p.left)
      (Spec.algebraMap ((T : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T))
      (by
        have hp : p.left ≫ X.hom = Spec.algebraMap _ _ := Over.w p
        change (Spec.map _ ≫ p.left) ≫ X.hom = _
        erw [Category.assoc, hp]
        change Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST)) ≫
            Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelDiagonal K S)) =
          Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelDiagonal K T)) ≫
            Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
          (numberFieldAdeleLevelDiagonal_natural K hST)))
    (by
      change _ ≫ pullback.snd _ _ = Spec.algebraMap _ _
      exact pullback.lift_snd _ _ _)

/-- Projection to the original model is the original full-level coefficient restriction. -/
@[simp]
theorem numberFieldLevelModelTransition_left_fst
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) :
    (numberFieldLevelModelTransition K hST X p).left ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))) =
        Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST)) ≫ p.left := by
  exact pullback.lift_fst _ _ _

/-- The full-level transition respects the original T-integer structure map. -/
@[simp]
theorem numberFieldLevelModelTransition_left_snd
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) :
    (numberFieldLevelModelTransition K hST X p).left ≫
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))) =
        Spec.algebraMap ((T : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T) := by
  exact pullback.lift_snd _ _ _

end NumberField

end Langlands.Global
