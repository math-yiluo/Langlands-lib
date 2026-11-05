import Langlands.Global.AdelicLevelModelClosedImmersionStatement
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs

/-! # Closed embeddings on actual arithmetic-level model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Closed model immersions remain closed embeddings after local base change. -/
private theorem localModelPointMap_isClosedEmbedding
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    [TopologicalSpace R] [IsLocalRing R] [ContinuousMul R] [IsOpenUnits R]
    [T2Space R] {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    letI := schemePointTopology R (ringBaseChange C R X) R
    letI := schemePointTopology R (ringBaseChange C R Y) R
    IsClosedEmbedding (X := RingPoint R (ringBaseChange C R X) R)
      (Y := RingPoint R (ringBaseChange C R Y) R)
      (fun p : RingPoint R (ringBaseChange C R X) R =>
      (p ≫ (Over.pullback (Spec.algebraMap C R)).map f :
        RingPoint R (ringBaseChange C R Y) R)) := by
  let g := (Over.pullback (Spec.algebraMap C R)).map f
  let : IsClosedImmersion g.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (Spec.algebraMap C R) f inferInstance
  exact isClosedEmbedding_schemeClosedPointMap R R g

/-- Coefficient restriction and local base change commute with postcomposition. -/
private theorem localModelPointMap_natural
    (C A R : Type u) [CommRing C] [CommRing A] [CommRing R]
    [Algebra C A] [Algebra C R]
    (g : A →ₐ[C] R) {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (p : RingPoint C X A) :
    ringPointBaseChangeEquiv C R R Y (RingPoint.changeRing g (p ≫ f)) =
      ringPointBaseChangeEquiv C R R X (RingPoint.changeRing g p) ≫
        (Over.pullback (Spec.algebraMap C R)).map f := by
  rw [show RingPoint.changeRing g (p ≫ f) =
    RingPoint.changeRing g p ≫ f from (Category.assoc _ _ _).symm]
  exact ringPointBaseChangeEquiv_natural C R R f _

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
variable (f : X ⟶ Y) [IsClosedImmersion f.left]
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- The actual curve-place level postcomposition is a closed embedding. -/
theorem curvePlaceLevelModelPointMap_isClosedEmbedding :
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := curvePlaceLevelModelPointTopology k F S Y
    IsClosedEmbedding
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))) := by
  let : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  let : QuasiCompact X.hom := by
    rw [← Over.w f]
    infer_instance
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S X
  let : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S Y
  let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
        (CurvePlaceLevelFactor k F S i)) := schemePointTopology _ _ _
  let (i : CurvePlaceLevelFactorIndex k F S) : TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
        (CurvePlaceLevelFactor k F S i)) := schemePointTopology _ _ _
  let (i : CurvePlaceLevelFactorIndex k F S) : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
    adelicLocalFactorUnits.1 k F S i
  let (i : CurvePlaceLevelFactorIndex k F S) : T2Space (CurvePlaceLevelFactor k F S i) := by
    cases i with
    | inl v => exact inferInstanceAs (T2Space (curvePlaceCompletion v.1))
    | inr v => exact inferInstanceAs (T2Space (curvePlaceCompletionIntegers v.1))
  have hX := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S X
  have hY := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S Y
  have hlocal := IsClosedEmbedding.piMap
    (A := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i))
    (B := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
      (CurvePlaceLevelFactor k F S i))
    (fun i =>
    localModelPointMap_isClosedEmbedding (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) f)
  apply IsClosedEmbedding.of_comp hY.isEmbedding
  have h := hlocal.comp hX.isClosedEmbedding
  convert h using 1
  funext p i
  exact localModelPointMap_natural (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S)
    (CurvePlaceLevelFactor k F S i) (curvePlaceLevelFactorAlgHom k F S i) f p

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
variable (f : X ⟶ Y) [IsClosedImmersion f.left]
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- The full number-field level postcomposition is a closed embedding. -/
theorem numberFieldLevelModelPointMap_isClosedEmbedding :
    letI := numberFieldLevelModelPointTopology K S X
    letI := numberFieldLevelModelPointTopology K S Y
    IsClosedEmbedding
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))) := by
  let : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  let : QuasiCompact X.hom := by
    rw [← Over.w f]
    infer_instance
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S X
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S Y
  let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
        (NumberFieldLevelFactor K S i)) := schemePointTopology _ _ _
  let (i : NumberFieldLevelFactorIndex K S) : TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
        (NumberFieldLevelFactor K S i)) := schemePointTopology _ _ _
  let (i : NumberFieldLevelFactorIndex K S) : IsOpenUnits (NumberFieldLevelFactor K S i) :=
    adelicLocalFactorUnits.2 K S i
  let (i : NumberFieldLevelFactorIndex K S) : T2Space (NumberFieldLevelFactor K S i) := by
    cases i with
    | inl v => exact inferInstanceAs (T2Space (InfiniteCompletion K v))
    | inr j =>
      cases j with
      | inl v => exact inferInstanceAs (T2Space (FiniteCompletion K v.1))
      | inr v => exact inferInstanceAs (T2Space (v.1.adicCompletionIntegers K))
  have hX := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S X
  have hY := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S Y
  have hlocal := IsClosedEmbedding.piMap
    (A := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i))
    (B := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
      (NumberFieldLevelFactor K S i))
    (fun i =>
    localModelPointMap_isClosedEmbedding ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) f)
  apply IsClosedEmbedding.of_comp hY.isEmbedding
  have h := hlocal.comp hX.isClosedEmbedding
  convert h using 1
  funext p i
  exact localModelPointMap_natural ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S)
    (NumberFieldLevelFactor K S i) (numberFieldLevelFactorAlgHom K S i) f p

end NumberField

/-- The exact level closed-immersion statement in both global-field cases. -/
theorem adelicLevelModelClosedImmersion : AdelicLevelModelClosedImmersionStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X Y f _ _ _
    exact curvePlaceLevelModelPointMap_isClosedEmbedding k F S f
  · intro K _ _ S X Y f _ _ _
    exact numberFieldLevelModelPointMap_isClosedEmbedding K S f

end Langlands.Global
