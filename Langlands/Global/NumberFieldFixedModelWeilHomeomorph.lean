import Langlands.Global.NumberFieldFixedLevelWeilEvaluation
import Langlands.Global.AdelicWeilLevelCofinality
import Langlands.Global.AdelicFixedModelPointComparisonProof
import Langlands.AlgebraicGeometry.PointTopology.FinalCoconeHomeomorph
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionFiniteType
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField Langlands.Global Langlands.Global.NumberFieldSIntegers

namespace Langlands.Global.NumberFieldFixedModelWeilHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open NumberFieldSIntegerFixedLevelRegroup AdelicWeilLevelCofinality

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  [LocallyOfFinitePresentation X.hom]

/-- The cocone on actual full-adele model points is an actual colimit. -/
def pointCoconeIsColimit :
    IsColimit (ringPointCocone ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOverDiagram K S) X (numberFieldAdeleOverCocone K S)) := by
  apply Nonempty.some
  apply (Types.isColimit_iff_coconeTypesIsColimit _).mpr
  exact ⟨((numberFieldFixedModelPointComparisonProperties K S X).2 inferInstance).2.1⟩

variable (L : Type u) [Field L] [NumberField L] [Algebra K L]
  (Y : Over (Spec (CommRingCat.of
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L))))
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom)

/-- The original fixed-model stage homeomorphisms form a natural isomorphism
along the actual full-preimage support functor. -/
def stageNatIso :
    numberFieldFixedModelPointDiagram K S
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) Y) ≅
      numberFieldUpperLevelFunctor K L S ⋙
        numberFieldFixedModelPointDiagram L (numberFieldExceptionalPreimage (L := L) S) Y := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  refine NatIso.ofComponents
    (fun T => by
      letI := numberFieldFixedModelStageTopology K S
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
          (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) Y) T
      letI := numberFieldFixedModelStageTopology L
        (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
      exact (adelicLevelPointHomeomorph K L S T Y n j hj).toEquiv.toIso) ?_
  intro T U f
  ext p
  exact (NumberFieldFixedLevelWeilEvaluation.levelPoint_natural
    K L S T Y n j hj U (leOfHom f) p)

/-- Original fixed integral-model Weil restriction commutes with the actual full
number-field adelic point spaces and their independently defined topologies. -/
def adelicPointHomeomorph :
    @Homeomorph
      (NumberFieldFixedModelAdelePoints K S
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
          (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) Y))
      (NumberFieldFixedModelAdelePoints L (numberFieldExceptionalPreimage (L := L) S) Y)
      (numberFieldFixedModelAdelePointTopology K S
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
          (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) Y))
      (numberFieldFixedModelAdelePointTopology L
        (numberFieldExceptionalPreimage (L := L) S) Y) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  exact finalCoconeHomeomorph
    (numberFieldFixedModelPointDiagram K S
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) Y))
    (numberFieldFixedModelPointDiagram L (numberFieldExceptionalPreimage (L := L) S) Y)
    (numberFieldUpperLevelFunctor K L S)
    (ringPointCocone ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOverDiagram K S)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) Y) (numberFieldAdeleOverCocone K S))
    (ringPointCocone
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L)
      (numberFieldAdeleLevelOverDiagram L (numberFieldExceptionalPreimage (L := L) S)) Y
      (numberFieldAdeleOverCocone L (numberFieldExceptionalPreimage (L := L) S)))
    (pointCoconeIsColimit K S _)
    (pointCoconeIsColimit L (numberFieldExceptionalPreimage (L := L) S) Y)
    (stageNatIso K S L Y n j hj)
    (numberFieldFixedModelStageTopology K S _)
    (numberFieldFixedModelStageTopology L (numberFieldExceptionalPreimage (L := L) S) Y)
    (fun {T U} f => (numberFieldFixedModelTransitionTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y T U (leOfHom f)).1)
    (fun T => by
      let := numberFieldFixedModelStageTopology K S
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
          (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) Y) T
      let := numberFieldFixedModelStageTopology L
        (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
      exact (adelicLevelPointHomeomorph K L S T Y n j hj).isHomeomorph)

/-- The full adelic homeomorphism restricts to the original homeomorphism at
every enlarged support and its full upper preimage. -/
@[simp]
theorem adelicPointHomeomorph_stage (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K)
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T)) :
    letI : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
    letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
    adelicPointHomeomorph K S L Y n j hj
      (p.changeRing (numberFieldAdeleLevelOverι K S T).hom) =
        (adelicLevelPointHomeomorph K L S T Y n j hj p).changeRing
          (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S)
            (upperLevel K L S T)).hom := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  unfold adelicPointHomeomorph
  apply finalCoconeHomeomorph_ι
  intro U V f
  exact (numberFieldFixedModelTransitionTopology L
    (numberFieldExceptionalPreimage (L := L) S) Y U V (leOfHom f)).1

end Langlands.Global.NumberFieldFixedModelWeilHomeomorph
