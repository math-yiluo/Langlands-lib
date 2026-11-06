import Langlands.Global.CurvePlaceProjectiveWeilAdeleHomeomorph
import Langlands.Global.CurvePlaceFixedModelWeilEvaluation
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionGenericFiberEvaluation

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open IntermediateField
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData

namespace Langlands.Global.CurvePlaceProjectiveWeilAdeleEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlaceProjectiveWeilAdeleHomeomorph

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L]

-- Derive the upper presentation without imposing a further hypothesis on L.
set_option quotPrecheck false in
local notation "withUpper% " t:0 =>
  (letI : Algebra (RatFunc k) L :=
    ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
   letI : IsScalarTower (RatFunc k) K L :=
    .of_algebraMap_eq fun _ => rfl
   letI : IsScalarTower k (RatFunc k) L :=
    .of_algebraMap_eq fun a => by
      change algebraMap k L a =
        algebraMap K L (algebraMap (RatFunc k) K (algebraMap k (RatFunc k) a))
      rw [← IsScalarTower.algebraMap_apply k (RatFunc k) K,
        ← IsScalarTower.algebraMap_apply k K L]
   letI : FunctionField k L := Module.Finite.trans (R := RatFunc k) K L
   t)

/-- The literal full curve adele inclusion preserves the original field coefficients. -/
theorem adeleInclusion_compatible :
    withUpper% (curvePlaceAdeleInclusion k K L).comp
        (algebraMap K (CurvePlaceAdeleRing k K)) =
      (algebraMap L (CurvePlaceAdeleRing k L)).comp (algebraMap K L) := withUpper% by
  apply RingHom.ext
  intro a
  exact curvePlaceAdeleInclusion_diagonal (k := k) (K := K) (L := L) a

variable (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

local instance originalLocallyOfFiniteType :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

/-- Evaluation of the original field Weil counit along the literal full curve adele inclusion. -/
def adelicEvaluation
    (p : CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    withUpper% CurvePlaceAdelePoints k L (originalScheme L X n j) := withUpper%
  weilRestrictionEvaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
    (curvePlaceAdeleInclusion k K L) (adeleInclusion_compatible k K L)
    (originalScheme L X n j) p

variable (s : K) [FiniteDimensional k⟮s⟯ K]
  (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
  (M : CurvePlacePrincipalProjectiveModelData k K L s S T X n j)

local instance denominatorNonzero : Fact (M.denominator ≠ 0) := ⟨M.denominator_ne_zero⟩

local notation "E" => curvePlacePrincipalExceptional k K s (M.denominator : K)

set_option maxHeartbeats 800000 in
/-- On original model points the field counit is integral evaluation followed by the upper identification. -/
theorem adelicEvaluation_model
    (p : CurvePlaceFixedModelAdelePoints k K E (lowerModel k K L s S T X n j M)) :
    withUpper% adelicEvaluation k K L X n j
        (curvePlaceSpreadAdelePointEquiv k K E (lowerModel k K L s S T X n j M) _
          (lowerGenericFiberIso k K L s S T X n j M) p) =
      curvePlaceSpreadAdelePointEquiv k L
        (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
        (upperGenericFiberIso k K L s S T X n j M)
        (CurvePlaceFixedModelWeilEvaluation.adelicEvaluation k K L s M.denominator
          M.geometric.asOver p) := withUpper% by
  let algAK : Algebra (curvePlaceSIntegers k K E) K :=
    (curvePlaceSIntegers k K E).subtype.toAlgebra
  let algAR : Algebra (curvePlaceSIntegers k K E) (curvePlaceAdeleOver k K E) :=
    (curvePlaceAdeleOver k K E).algebra
  let algKR : Algebra K (curvePlaceAdeleOver k K E) :=
    inferInstanceAs (Algebra K (CurvePlaceAdeleRing k K))
  let towerKR := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algAK algKR algAR
    (curvePlaceAdeleLevelDiagonal_eq k K E)
  let algBL : Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) E)) L :=
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) E)).subtype.toAlgebra
  let algBE : Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) E))
      (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) E)) :=
    (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) E)).algebra
  let algLE : Algebra L
      (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) E)) :=
    inferInstanceAs (Algebra L (CurvePlaceAdeleRing k L))
  let towerLE := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algBL algLE algBE
    (curvePlaceAdeleLevelDiagonal_eq k L (curvePlaceExceptionalPreimage (L := L) E))
  have h := projectiveModelWeilGenericFiberEvaluation_eq_integral
    (curvePlaceSIntegers k K E)
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) E)) K L
    (curvePlaceAdeleOver k K E)
    (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) E))
    (curvePlaceAdeleInclusion k K L) (adeleInclusion_compatible k K L) M.geometric p
  dsimp only [adelicEvaluation, CurvePlaceFixedModelWeilEvaluation.adelicEvaluation,
    curvePlaceSpreadAdelePointEquiv, Equiv.trans_apply, Iso.homCongr,
    curvePlaceGenericFiberAdelePointEquiv, lowerGenericFiberIso,
    curvePlacePrincipalProjectiveModelWeilGenericFiberIso, upperGenericFiberIso]
  dsimp only [projectiveModelWeilGenericFiberEvaluation] at h
  simp only [Iso.refl_inv, Category.id_comp]
  convert h using 1 <;> rfl

local instance modelImmersion : IsImmersion M.geometric.immersion :=
  M.geometric.isImmersion

local instance modelCompact : CompactSpace M.geometric.asOver.left :=
  QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom

/-- The original-field full curve adelic homeomorphism is the canonical Weil evaluation. -/
theorem adelicPointHomeomorph_eq_evaluation
    (p : CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    withUpper% adelicPointHomeomorph k K L s S T X n j M p =
      adelicEvaluation k K L X n j p := withUpper% by
  obtain ⟨q, rfl⟩ :=
    (curvePlaceSpreadAdelePointEquiv k K E (lowerModel k K L s S T X n j M) _
      (lowerGenericFiberIso k K L s S T X n j M)).surjective p
  rw [CurvePlaceProjectiveWeilAdeleHomeomorph.adelicPointHomeomorph_model,
    CurvePlaceFixedModelWeilEvaluation.adelicPointHomeomorph_eq_evaluation,
    adelicEvaluation_model]

/-- For arbitrary independent finite-type spreads the same homeomorphism is canonical evaluation. -/
theorem adelicPointHomeomorphOfSpreads_eq_evaluation
    (U : Finset (AlgebraicCurve.Place k K)) (V : Finset (AlgebraicCurve.Place k L))
    (P : Over (Spec (CommRingCat.of (curvePlaceSIntegers k K U))))
    (Q : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L V))))
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (e : curvePlaceModelGenericFiber k K U P ≅
      affineChartWeilRestriction K L (originalScheme L X n j))
    (f : curvePlaceModelGenericFiber k L V Q ≅ originalScheme L X n j)
    (p : CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    withUpper% adelicPointHomeomorphOfSpreads k K L s S T X n j M U V P Q e f p =
      adelicEvaluation k K L X n j p := withUpper% by
  rw [adelicPointHomeomorphOfSpreads_apply]
  exact adelicPointHomeomorph_eq_evaluation k K L X n j s S T M p

/-- Changing the parameter, supports and constructed arithmetic model preserves the entire field map. -/
theorem adelicPointHomeomorph_independent_model
    (s' : K) [FiniteDimensional k⟮s'⟯ K]
    (S' : Finset (AlgebraicCurve.Place k K)) (T' : Finset (AlgebraicCurve.Place k L))
    (M' : CurvePlacePrincipalProjectiveModelData k K L s' S' T' X n j)
    (p : CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j))) :
    withUpper% adelicPointHomeomorph k K L s S T X n j M p =
      adelicPointHomeomorph k K L s' S' T' X n j M' p := withUpper% by
  rw [adelicPointHomeomorph_eq_evaluation, adelicPointHomeomorph_eq_evaluation]

end Langlands.Global.CurvePlaceProjectiveWeilAdeleEvaluation
