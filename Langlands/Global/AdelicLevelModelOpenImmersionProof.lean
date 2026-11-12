import Langlands.Global.AdelicLevelModelOpenImmersionStatement
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.Global.AdelicUnitLocusProof
import Langlands.Global.AdelicNonunitSequence
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-! # Open immersions on actual arithmetic-level model points -/

noncomputable section

universe u

open CategoryTheory Topology Filter
open _root_.AlgebraicGeometry

namespace Langlands.Global.AdelicLevelModelOpenImmersionProof

open Langlands.AlgebraicGeometry.PointTopology

/-- Open model immersions remain open embeddings after local base change. -/
theorem localModelPointMap_isOpenEmbedding
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R]
    {X Y : Over (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) [IsOpenImmersion f.left] :
    letI := schemePointTopology R (ringBaseChange C R X) R
    letI := schemePointTopology R (ringBaseChange C R Y) R
    IsOpenEmbedding (X := RingPoint R (ringBaseChange C R X) R)
      (Y := RingPoint R (ringBaseChange C R Y) R)
      (fun p : RingPoint R (ringBaseChange C R X) R =>
      (p ≫ (Over.pullback (Spec.algebraMap C R)).map f :
        RingPoint R (ringBaseChange C R Y) R)) := by
  let g := (Over.pullback (Spec.algebraMap C R)).map f
  let : IsOpenImmersion g.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.algebraMap C R) f inferInstance
  exact isOpenEmbedding_schemePointMap R R g

/-- Coefficient restriction and local base change commute with postcomposition. -/
theorem localModelPointMap_natural
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

/-- Postcomposition with an open immersion is injective on points. -/
theorem postcomp_injective (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) [IsOpenImmersion f.left] :
    Function.Injective (fun p : RingPoint C X A => (p ≫ f : RingPoint C Y A)) := by
  intro p q h
  dsimp only [RingPoint] at p q h
  apply Over.OverMorphism.ext
  have h' := congrArg CommaMorphism.left h
  simp only [Over.comp_left] at h'
  exact (cancel_mono f.left).mp h'

end Langlands.Global.AdelicLevelModelOpenImmersionProof

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Global.AdelicLevelModelOpenImmersionProof

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The actual curve-place level postcomposition with an open immersion is an embedding. -/
theorem curvePlaceLevelModelPointMap_isEmbedding_of_isOpenImmersion
    {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (f : X ⟶ Y) [IsOpenImmersion f.left] :
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := curvePlaceLevelModelPointTopology k F S Y
    IsEmbedding
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))) := by
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
  have hX := curvePlaceLevelModelPointMap_isInducing k F S X
  have hY := curvePlaceLevelModelPointMap_isInducing k F S Y
  have hlocal := IsEmbedding.piMap
    (A := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i))
    (B := fun i => RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) Y)
      (CurvePlaceLevelFactor k F S i))
    (fun i =>
    (localModelPointMap_isOpenEmbedding (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S i) f).isEmbedding)
  have hind : IsInducing (curvePlaceLevelModelPointMap k F S Y ∘
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S)))) := by
    convert hlocal.isInducing.comp hX using 1
    funext p i
    exact localModelPointMap_natural (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S)
      (CurvePlaceLevelFactor k F S i) (curvePlaceLevelFactorAlgHom k F S i) f p
  have hcont := hY.continuous_iff.mpr hind.continuous
  exact ⟨IsInducing.of_comp hcont hY.continuous hind,
    postcomp_injective (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) f⟩

/-- A level element with one zero coordinate and all other coordinates one. -/
def curvePlaceLevelNonunitSequence (n : ℕ) : curvePlaceAdeleLevel k F S :=
  ⟨curvePlaceNonunitSequence k F n, by
    intro v _
    change restrictedZeroAtPlace (fun v : AlgebraicCurve.Place k F =>
      (curvePlaceCompletionIntegers v).toSubring) (curvePlaceNonunitPlaceSequence k F n) v ∈ _
    rw [restrictedZeroAtPlace_apply]
    split
    · exact (curvePlaceCompletionIntegers v).zero_mem
    · exact (curvePlaceCompletionIntegers v).one_mem⟩

/-- The punctured affine line has non-open image on curve-place level points. -/
theorem curvePlaceLevel_puncture_not_isOpen :
    ¬ IsOpen[curvePlaceLevelModelPointTopology k F S
        (ringTest (curvePlaceSIntegers k F S) (MvPolynomial Unit (curvePlaceSIntegers k F S)))]
      (Set.range (fun p : RingPoint (curvePlaceSIntegers k F S)
          (affineLinePuncture (curvePlaceSIntegers k F S)) (curvePlaceAdeleLevel k F S) =>
        (p ≫ affineLinePunctureι (curvePlaceSIntegers k F S) :
          RingPoint (curvePlaceSIntegers k F S)
            (ringTest (curvePlaceSIntegers k F S)
              (MvPolynomial Unit (curvePlaceSIntegers k F S)))
            (curvePlaceAdeleLevel k F S)))) := by
  rw [curvePlaceLevelModelPointTopology_eq_affine]
  refine (affineLineUnitLocusObstruction_of_nonunit_tendsto (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevel k F S) (curvePlaceLevelNonunitSequence k F S) ?_ ?_).2.2
  · intro n h
    exact curvePlaceNonunitSequence_not_isUnit k F n
      (h.map (curvePlaceAdeleLevel k F S).subtype)
  · exact tendsto_subtype_rng.mpr (tendsto_curvePlaceNonunitSequence k F)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- The full number-field level postcomposition with an open immersion is an embedding. -/
theorem numberFieldLevelModelPointMap_isEmbedding_of_isOpenImmersion
    {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (f : X ⟶ Y) [IsOpenImmersion f.left] :
    letI := numberFieldLevelModelPointTopology K S X
    letI := numberFieldLevelModelPointTopology K S Y
    IsEmbedding
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevel K S))) := by
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
  have hX := numberFieldLevelModelPointMap_isInducing K S X
  have hY := numberFieldLevelModelPointMap_isInducing K S Y
  have hlocal := IsEmbedding.piMap
    (A := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i))
    (B := fun i => RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) Y)
      (NumberFieldLevelFactor K S i))
    (fun i =>
    (localModelPointMap_isOpenEmbedding ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S i) f).isEmbedding)
  have hind : IsInducing (numberFieldLevelModelPointMap K S Y ∘
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevel K S)))) := by
    convert hlocal.isInducing.comp hX using 1
    funext p i
    exact localModelPointMap_natural ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S i)
      (numberFieldLevelFactorAlgHom K S i) f p
  have hcont := hY.continuous_iff.mpr hind.continuous
  exact ⟨IsInducing.of_comp hcont hY.continuous hind,
    postcomp_injective ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) f⟩

/-- A full level element with every infinite coordinate one, one zero finite coordinate and
all other finite coordinates one. -/
def numberFieldLevelNonunitSequence (n : ℕ) : numberFieldAdeleLevel K S :=
  ⟨numberFieldNonunitSequence K n, by
    intro v _
    change restrictedZeroAtPlace (fun v : FinitePlace K => (v.adicCompletionIntegers K).toSubring)
      (numberFieldNonunitPlaceSequence K n) v ∈ _
    rw [restrictedZeroAtPlace_apply]
    split
    · exact (v.adicCompletionIntegers K).zero_mem
    · exact (v.adicCompletionIntegers K).one_mem⟩

/-- The punctured affine line has non-open image on full number-field level points. -/
theorem numberFieldLevel_puncture_not_isOpen :
    ¬ IsOpen[numberFieldLevelModelPointTopology K S
        (ringTest ((S : Set (FinitePlace K)).integer K)
          (MvPolynomial Unit ((S : Set (FinitePlace K)).integer K)))]
      (Set.range (fun p : RingPoint ((S : Set (FinitePlace K)).integer K)
          (affineLinePuncture ((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleLevel K S) =>
        (p ≫ affineLinePunctureι ((S : Set (FinitePlace K)).integer K) :
          RingPoint ((S : Set (FinitePlace K)).integer K)
            (ringTest ((S : Set (FinitePlace K)).integer K)
              (MvPolynomial Unit ((S : Set (FinitePlace K)).integer K)))
            (numberFieldAdeleLevel K S)))) := by
  rw [numberFieldLevelModelPointTopology_eq_affine]
  refine (affineLineUnitLocusObstruction_of_nonunit_tendsto ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevel K S) (numberFieldLevelNonunitSequence K S) ?_ ?_).2.2
  · intro n h
    exact numberFieldNonunitSequence_not_isUnit K n
      (h.map (numberFieldAdeleLevel K S).subtype)
  · exact tendsto_subtype_rng.mpr (tendsto_numberFieldNonunitSequence K)

end NumberField

/-- The exact level open-immersion statement in both global-field cases. -/
theorem adelicLevelModelOpenImmersion : AdelicLevelModelOpenImmersionStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S
    exact ⟨fun X Y f _ _ _ => curvePlaceLevelModelPointMap_isEmbedding_of_isOpenImmersion k F S f,
      curvePlaceLevel_puncture_not_isOpen k F S⟩
  · intro K _ _ S
    exact ⟨fun X Y f _ _ _ => numberFieldLevelModelPointMap_isEmbedding_of_isOpenImmersion K S f,
      numberFieldLevel_puncture_not_isOpen K S⟩

end Langlands.Global
