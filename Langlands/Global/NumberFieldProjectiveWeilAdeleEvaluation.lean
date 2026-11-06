import Langlands.Global.NumberFieldProjectiveWeilAdeleHomeomorph
import Langlands.Global.NumberFieldFixedModelWeilEvaluation
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionGenericFiberEvaluation

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData

namespace Langlands.Global.NumberFieldProjectiveWeilAdeleEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open NumberFieldProjectiveWeilAdeleHomeomorph AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- The literal full adele inclusion preserves the original field coefficients. -/
theorem adeleInclusion_compatible :
    (adeleInclusion (K := K) (L := L)).comp (algebraMap K (Adeles K)) =
      (algebraMap L (Adeles L)).comp (algebraMap K L) := by
  apply RingHom.ext
  intro a
  exact adeleInclusion_diagonal (K := K) (L := L) a

variable (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

local instance originalLocallyOfFiniteType :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

/-- Evaluation of the original field Weil counit along the literal full adele inclusion. -/
def adelicEvaluation
    (p : NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    NumberFieldAdelePoints L (originalScheme L X n j) :=
  weilRestrictionEvaluation K L (Adeles K) (Adeles L)
    (adeleInclusion (K := K) (L := L)) (adeleInclusion_compatible K L)
    (originalScheme L X n j) p

variable (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L))
  (M : NumberFieldExtensionProjectiveModelData K L S T X n j)

set_option maxHeartbeats 800000 in
/-- On original model points the field counit is integral evaluation followed by the upper identification. -/
theorem adelicEvaluation_model
    (p : NumberFieldFixedModelAdelePoints K M.exceptional (lowerModel K L S T X n j M)) :
    adelicEvaluation K L X n j
        (numberFieldSpreadAdelePointEquiv K M.exceptional (lowerModel K L S T X n j M) _
          (lowerGenericFiberIso K L S T X n j M) p) =
      numberFieldSpreadAdelePointEquiv L
        (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
        (upperGenericFiberIso K L S T X n j M)
        (NumberFieldFixedModelWeilEvaluation.adelicEvaluation K L M.exceptional
          M.geometric.asOver p) := by
  let algAK : Algebra ((M.exceptional : Set (FinitePlace K)).integer K) K :=
    ((M.exceptional : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algAR : Algebra ((M.exceptional : Set (FinitePlace K)).integer K)
      (numberFieldAdeleOver K M.exceptional) := (numberFieldAdeleOver K M.exceptional).algebra
  let algKR : Algebra K (numberFieldAdeleOver K M.exceptional) :=
    inferInstanceAs (Algebra K (Adeles K))
  let towerKR := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algAK algKR algAR (fun _ => rfl)
  let algBL : Algebra
      (((numberFieldExceptionalPreimage (L := L) M.exceptional : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) L :=
    (((numberFieldExceptionalPreimage (L := L) M.exceptional : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L).toSubring.subtype.toAlgebra
  let algBE : Algebra
      (((numberFieldExceptionalPreimage (L := L) M.exceptional : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L)
      (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) M.exceptional)) :=
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) M.exceptional)).algebra
  let algLE : Algebra L
      (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) M.exceptional)) :=
    inferInstanceAs (Algebra L (Adeles L))
  let towerLE := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algBL algLE algBE (fun _ => rfl)
  have h := projectiveModelWeilGenericFiberEvaluation_eq_integral
    ((M.exceptional : Set (FinitePlace K)).integer K)
    (((numberFieldExceptionalPreimage (L := L) M.exceptional : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) K L
    (numberFieldAdeleOver K M.exceptional)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) M.exceptional))
    (adeleInclusion (K := K) (L := L)) (adeleInclusion_compatible K L) M.geometric p
  exact h

local instance modelImmersion : IsImmersion M.geometric.immersion :=
  M.geometric.isImmersion

local instance modelCompact : CompactSpace M.geometric.asOver.left :=
  QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom

/-- The original-field full adelic homeomorphism is the canonical Weil evaluation. -/
theorem adelicPointHomeomorph_eq_evaluation
    (p : NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    adelicPointHomeomorph K L S T X n j M p = adelicEvaluation K L X n j p := by
  obtain ⟨q, rfl⟩ :=
    (numberFieldSpreadAdelePointEquiv K M.exceptional (lowerModel K L S T X n j M) _
      (lowerGenericFiberIso K L S T X n j M)).surjective p
  rw [NumberFieldProjectiveWeilAdeleHomeomorph.adelicPointHomeomorph_model,
    NumberFieldFixedModelWeilEvaluation.adelicPointHomeomorph_eq_evaluation,
    adelicEvaluation_model]

/-- For arbitrary independent finite-type spreads the same homeomorphism is canonical evaluation. -/
theorem adelicPointHomeomorphOfSpreads_eq_evaluation
    (U : Finset (FinitePlace K)) (V : Finset (FinitePlace L))
    (P : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    (Q : Over (Spec (CommRingCat.of ((V : Set (FinitePlace L)).integer L))))
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (e : numberFieldModelGenericFiber K U P ≅
      affineChartWeilRestriction K L (originalScheme L X n j))
    (f : numberFieldModelGenericFiber L V Q ≅ originalScheme L X n j)
    (p : NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    adelicPointHomeomorphOfSpreads K L S T X n j M U V P Q e f p =
      adelicEvaluation K L X n j p := by
  rw [adelicPointHomeomorphOfSpreads_apply]
  exact adelicPointHomeomorph_eq_evaluation K L X n j S T M p

/-- Changing the constructed arithmetic model preserves the entire original-field map. -/
theorem adelicPointHomeomorph_independent_model
    (S' : Finset (FinitePlace K)) (T' : Finset (FinitePlace L))
    (M' : NumberFieldExtensionProjectiveModelData K L S' T' X n j)
    (p : NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    adelicPointHomeomorph K L S T X n j M p =
      adelicPointHomeomorph K L S' T' X n j M' p := by
  rw [adelicPointHomeomorph_eq_evaluation, adelicPointHomeomorph_eq_evaluation]

end Langlands.Global.NumberFieldProjectiveWeilAdeleEvaluation
