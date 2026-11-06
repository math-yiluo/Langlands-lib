import Langlands.Global.CurvePlaceFixedModelWeilHomeomorph
import Langlands.Global.AdelicGenericFiberPoints
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.AlgebraicGeometry.PointTopology.ProjectiveModelWeilGenericFiber

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open IntermediateField
open scoped Langlands.Global.CurvePlacePrincipalSIntegers
  AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData

namespace Langlands.Global.CurvePlaceProjectiveWeilAdeleHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
  (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

-- Derive the upper presentation in both declaration types and proof terms.
-- It supplies no additional hypothesis on L.
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

/-- The original upper field scheme with its specified projective structure map. -/
abbrev originalScheme : Over (Spec (CommRingCat.of L)) :=
  Over.mk (j ≫ projectiveSpaceToSpec L n)

local instance originalLocallyOfFiniteType :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

variable (M : CurvePlacePrincipalProjectiveModelData k K L s S T X n j)

local instance denominatorNonzero : Fact (M.denominator ≠ 0) := ⟨M.denominator_ne_zero⟩

local notation "E" => curvePlacePrincipalExceptional k K s (M.denominator : K)

/-- The original integral Weil model over the constructed lower exceptional set. -/
abbrev lowerModel :=
  affineChartWeilRestriction (curvePlaceSIntegers k K E)
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) E)) M.geometric.asOver

/-- The lower model's actual generic fiber is the Weil scheme of the original X. -/
def lowerGenericFiberIso :
    curvePlaceModelGenericFiber k K E (lowerModel k K L s S T X n j M) ≅
      affineChartWeilRestriction K L (originalScheme L X n j) :=
  curvePlacePrincipalProjectiveModelWeilGenericFiberIso k K L s S T X n j M

/-- The constructed upper model's actual generic fiber is the originally specified X. -/
def upperGenericFiberIso :
    curvePlaceModelGenericFiber k L
      (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver ≅
        originalScheme L X n j :=
  M.geometric.genericFiberIso

/-- The full adelic comparison on the original field schemes and their constructed spreads. -/
def adelicPointHomeomorph :
    withUpper% @Homeomorph
      (CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j)))
      (CurvePlaceAdelePoints k L (originalScheme L X n j))
      (curvePlaceSpreadAdelePointTopology k K E
        (lowerModel k K L s S T X n j M) _
        (lowerGenericFiberIso k K L s S T X n j M))
      (curvePlaceSpreadAdelePointTopology k L
        (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
        (upperGenericFiberIso k K L s S T X n j M)) := withUpper% by
  let : IsImmersion M.geometric.immersion := M.geometric.isImmersion
  let : CompactSpace M.geometric.asOver.left :=
    QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom
  letI := curvePlaceFixedModelAdelePointTopology k K E
    (lowerModel k K L s S T X n j M)
  letI := curvePlaceFixedModelAdelePointTopology k L
    (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver
  letI := curvePlaceSpreadAdelePointTopology k K E
    (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M)
  letI := curvePlaceSpreadAdelePointTopology k L
    (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
    (upperGenericFiberIso k K L s S T X n j M)
  exact (curvePlaceSpreadAdelePointHomeomorph k K E
      (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M)).symm.trans
    ((CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s M.denominator
      M.geometric.asOver n M.geometric.immersion rfl).trans
        (curvePlaceSpreadAdelePointHomeomorph k L
          (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
          (upperGenericFiberIso k K L s S T X n j M)))

local instance modelImmersion : IsImmersion M.geometric.immersion :=
  M.geometric.isImmersion

local instance modelCompact : CompactSpace M.geometric.asOver.left :=
  QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom

local instance modelSeparated : IsSeparated M.geometric.asOver.hom :=
  isSeparated_of_projectiveImmersion _ M.geometric.asOver n M.geometric.immersion rfl

local instance modelQuasiSeparated : QuasiSeparatedSpace M.geometric.asOver.left :=
  quasiSeparatedSpace_of_quasiSeparated M.geometric.asOver.hom

/-- On the original model points, the field comparison is the fixed-model comparison. -/
@[simp]
theorem adelicPointHomeomorph_model
    (p : CurvePlaceFixedModelAdelePoints k K E
      (lowerModel k K L s S T X n j M)) :
    withUpper% adelicPointHomeomorph k K L s S T X n j M
        (curvePlaceSpreadAdelePointEquiv k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M) p) =
      curvePlaceSpreadAdelePointEquiv k L
        (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
        (upperGenericFiberIso k K L s S T X n j M)
        (CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s M.denominator
          M.geometric.asOver n M.geometric.immersion rfl p) := withUpper% by
  change curvePlaceSpreadAdelePointEquiv k L _ _ _ _
    (CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s M.denominator
      M.geometric.asOver n M.geometric.immersion rfl
      ((curvePlaceSpreadAdelePointEquiv k K E
        (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M)).symm
        (curvePlaceSpreadAdelePointEquiv k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M) p))) = _
  rw [Equiv.symm_apply_apply]

/-- At every original arithmetic stage, the field map is the original level Weil map. -/
@[simp]
theorem adelicPointHomeomorph_stage (U : AdelicLevelIndexAbove E)
    (p : RingPoint (curvePlaceSIntegers k K E)
      (lowerModel k K L s S T X n j M) (curvePlaceAdeleLevelOver k K E U)) :
    withUpper% adelicPointHomeomorph k K L s S T X n j M
        (curvePlaceSpreadAdelePointEquiv k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M)
          (p.changeRing (curvePlaceAdeleLevelOverι k K E U).hom)) =
      curvePlaceSpreadAdelePointEquiv k L
        (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
        (upperGenericFiberIso k K L s S T X n j M)
        ((CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s M.denominator U
          M.geometric.asOver n M.geometric.immersion rfl p).changeRing
          (curvePlaceAdeleLevelOverι k L
            (curvePlaceExceptionalPreimage (L := L) E)
            (CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s M.denominator U)).hom) := withUpper% by
  rw [adelicPointHomeomorph_model,
    CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph_stage]

/-- Independently specified finite-type spreads give the same original comparison homeomorphism. -/
def adelicPointHomeomorphOfSpreads
    (U : Finset (AlgebraicCurve.Place k K)) (V : Finset (AlgebraicCurve.Place k L))
    (P : Over (Spec (CommRingCat.of (curvePlaceSIntegers k K U))))
    (Q : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L V))))
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (e : curvePlaceModelGenericFiber k K U P ≅
      affineChartWeilRestriction K L (originalScheme L X n j))
    (f : curvePlaceModelGenericFiber k L V Q ≅ originalScheme L X n j) :
    withUpper% @Homeomorph
      (CurvePlaceAdelePoints k K (affineChartWeilRestriction K L (originalScheme L X n j)))
      (CurvePlaceAdelePoints k L (originalScheme L X n j))
      (curvePlaceSpreadAdelePointTopology k K U P _ e)
      (curvePlaceSpreadAdelePointTopology k L V Q _ f) := withUpper% by
  let : CompactSpace M.geometric.asOver.left :=
    QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom
  let : QuasiCompact (lowerModel k K L s S T X n j M).hom :=
    affineChartWeilRestriction_quasiCompact _ _ M.geometric.asOver
      M.geometric.hasFiniteAffineNeighborhoods
  have hK := curvePlaceSpreadTopologyIndependence k K U E P
    (lowerModel k K L s S T X n j M) _ e (lowerGenericFiberIso k K L s S T X n j M)
  have hL := curvePlaceSpreadTopologyIndependence k L V
    (curvePlaceExceptionalPreimage (L := L) E) Q M.geometric.asOver _
    f (upperGenericFiberIso k K L s S T X n j M)
  letI := curvePlaceSpreadAdelePointTopology k K U P _ e
  letI := curvePlaceSpreadAdelePointTopology k L V Q _ f
  refine
    { toEquiv := @Homeomorph.toEquiv _ _
        (curvePlaceSpreadAdelePointTopology k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M))
        (curvePlaceSpreadAdelePointTopology k L
          (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
          (upperGenericFiberIso k K L s S T X n j M))
        (adelicPointHomeomorph k K L s S T X n j M)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [hK, hL]
    exact @Homeomorph.continuous_toFun _ _
        (curvePlaceSpreadAdelePointTopology k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M))
        (curvePlaceSpreadAdelePointTopology k L
          (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
          (upperGenericFiberIso k K L s S T X n j M))
        (adelicPointHomeomorph k K L s S T X n j M)
  · rw [hK, hL]
    exact @Homeomorph.continuous_invFun _ _
        (curvePlaceSpreadAdelePointTopology k K E
          (lowerModel k K L s S T X n j M) _ (lowerGenericFiberIso k K L s S T X n j M))
        (curvePlaceSpreadAdelePointTopology k L
          (curvePlaceExceptionalPreimage (L := L) E) M.geometric.asOver _
          (upperGenericFiberIso k K L s S T X n j M))
        (adelicPointHomeomorph k K L s S T X n j M)

/-- Changing the specified spreads preserves the entire underlying comparison map. -/
@[simp]
theorem adelicPointHomeomorphOfSpreads_apply
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
      adelicPointHomeomorph k K L s S T X n j M p := rfl

end Langlands.Global.CurvePlaceProjectiveWeilAdeleHomeomorph
