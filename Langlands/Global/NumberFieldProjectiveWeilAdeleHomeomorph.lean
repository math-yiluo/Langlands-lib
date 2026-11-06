import Langlands.Global.NumberFieldFixedModelWeilHomeomorph
import Langlands.Global.AdelicGenericFiberPoints
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.AlgebraicGeometry.PointTopology.ProjectiveModelWeilGenericFiber

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped Langlands.Global.NumberFieldSIntegers
  Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData

namespace Langlands.Global.NumberFieldProjectiveWeilAdeleHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L))
  (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

/-- The original upper field scheme with its specified projective structure map. -/
abbrev originalScheme : Over (Spec (CommRingCat.of L)) :=
  Over.mk (j ≫ projectiveSpaceToSpec L n)

local instance originalLocallyOfFiniteType :
    LocallyOfFiniteType (originalScheme L X n j).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

variable (M : NumberFieldExtensionProjectiveModelData K L S T X n j)

/-- The original integral Weil model over the constructed lower exceptional set. -/
abbrev lowerModel :=
  affineChartWeilRestriction ((M.exceptional : Set (FinitePlace K)).integer K)
    (((numberFieldExceptionalPreimage (L := L) M.exceptional :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) M.geometric.asOver

/-- The lower model's actual generic fiber is the Weil scheme of the original X. -/
def lowerGenericFiberIso :
    numberFieldModelGenericFiber K M.exceptional (lowerModel K L S T X n j M) ≅
      affineChartWeilRestriction K L (originalScheme L X n j) :=
  numberFieldProjectiveModelWeilGenericFiberIso K L S T X n j M

/-- The constructed upper model's actual generic fiber is the originally specified X. -/
def upperGenericFiberIso :
    numberFieldModelGenericFiber L
      (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver ≅
        originalScheme L X n j :=
  M.geometric.genericFiberIso

/-- The full adelic comparison on the original field schemes and their constructed spreads. -/
def adelicPointHomeomorph :
    @Homeomorph
      (NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j)))
      (NumberFieldAdelePoints L (originalScheme L X n j))
      (numberFieldSpreadAdelePointTopology K M.exceptional
        (lowerModel K L S T X n j M) _
        (lowerGenericFiberIso K L S T X n j M))
      (numberFieldSpreadAdelePointTopology L
        (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
        (upperGenericFiberIso K L S T X n j M)) := by
  let : IsImmersion M.geometric.immersion := M.geometric.isImmersion
  let : CompactSpace M.geometric.asOver.left :=
    QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom
  letI := numberFieldFixedModelAdelePointTopology K M.exceptional
    (lowerModel K L S T X n j M)
  letI := numberFieldFixedModelAdelePointTopology L
    (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver
  letI := numberFieldSpreadAdelePointTopology K M.exceptional
    (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M)
  letI := numberFieldSpreadAdelePointTopology L
    (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
    (upperGenericFiberIso K L S T X n j M)
  exact (numberFieldSpreadAdelePointHomeomorph K M.exceptional
      (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M)).symm.trans
    ((NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K M.exceptional L
      M.geometric.asOver n M.geometric.immersion rfl).trans
        (numberFieldSpreadAdelePointHomeomorph L
          (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
          (upperGenericFiberIso K L S T X n j M)))

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
    (p : NumberFieldFixedModelAdelePoints K M.exceptional
      (lowerModel K L S T X n j M)) :
    adelicPointHomeomorph K L S T X n j M
        (numberFieldSpreadAdelePointEquiv K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M) p) =
      numberFieldSpreadAdelePointEquiv L
        (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
        (upperGenericFiberIso K L S T X n j M)
        (NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K M.exceptional L
          M.geometric.asOver n M.geometric.immersion rfl p) := by
  change numberFieldSpreadAdelePointEquiv L _ _ _ _
    (NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K M.exceptional L
      M.geometric.asOver n M.geometric.immersion rfl
      ((numberFieldSpreadAdelePointEquiv K M.exceptional
        (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M)).symm
        (numberFieldSpreadAdelePointEquiv K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M) p))) = _
  rw [Equiv.symm_apply_apply]

/-- At every original arithmetic stage, the field map is the original level Weil map. -/
@[simp]
theorem adelicPointHomeomorph_stage (U : AdelicLevelIndexAbove M.exceptional)
    (p : RingPoint ((M.exceptional : Set (FinitePlace K)).integer K)
      (lowerModel K L S T X n j M) (numberFieldAdeleLevelOver K M.exceptional U)) :
    adelicPointHomeomorph K L S T X n j M
        (numberFieldSpreadAdelePointEquiv K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M)
          (p.changeRing (numberFieldAdeleLevelOverι K M.exceptional U).hom)) =
      numberFieldSpreadAdelePointEquiv L
        (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
        (upperGenericFiberIso K L S T X n j M)
        ((NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L M.exceptional U
          M.geometric.asOver n M.geometric.immersion rfl p).changeRing
          (numberFieldAdeleLevelOverι L
            (numberFieldExceptionalPreimage (L := L) M.exceptional)
            (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L M.exceptional U)).hom) := by
  rw [adelicPointHomeomorph_model,
    NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph_stage]

/-- Independently specified finite-type spreads give the same original comparison homeomorphism. -/
def adelicPointHomeomorphOfSpreads
    (U : Finset (FinitePlace K)) (V : Finset (FinitePlace L))
    (P : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    (Q : Over (Spec (CommRingCat.of ((V : Set (FinitePlace L)).integer L))))
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (e : numberFieldModelGenericFiber K U P ≅
      affineChartWeilRestriction K L (originalScheme L X n j))
    (f : numberFieldModelGenericFiber L V Q ≅ originalScheme L X n j) :
    @Homeomorph
      (NumberFieldAdelePoints K (affineChartWeilRestriction K L (originalScheme L X n j)))
      (NumberFieldAdelePoints L (originalScheme L X n j))
      (numberFieldSpreadAdelePointTopology K U P _ e)
      (numberFieldSpreadAdelePointTopology L V Q _ f) := by
  let : CompactSpace M.geometric.asOver.left :=
    QuasiCompact.compactSpace_of_compactSpace M.geometric.asOver.hom
  let : QuasiCompact (lowerModel K L S T X n j M).hom :=
    affineChartWeilRestriction_quasiCompact _ _ M.geometric.asOver
      M.geometric.hasFiniteAffineNeighborhoods
  have hK := numberFieldSpreadTopologyIndependence K U M.exceptional P
    (lowerModel K L S T X n j M) _ e (lowerGenericFiberIso K L S T X n j M)
  have hL := numberFieldSpreadTopologyIndependence L V
    (numberFieldExceptionalPreimage (L := L) M.exceptional) Q M.geometric.asOver _
    f (upperGenericFiberIso K L S T X n j M)
  letI := numberFieldSpreadAdelePointTopology K U P _ e
  letI := numberFieldSpreadAdelePointTopology L V Q _ f
  refine
    { toEquiv := @Homeomorph.toEquiv _ _
        (numberFieldSpreadAdelePointTopology K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M))
        (numberFieldSpreadAdelePointTopology L
          (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
          (upperGenericFiberIso K L S T X n j M))
        (adelicPointHomeomorph K L S T X n j M)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [hK, hL]
    exact @Homeomorph.continuous_toFun _ _
        (numberFieldSpreadAdelePointTopology K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M))
        (numberFieldSpreadAdelePointTopology L
          (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
          (upperGenericFiberIso K L S T X n j M))
        (adelicPointHomeomorph K L S T X n j M)
  · rw [hK, hL]
    exact @Homeomorph.continuous_invFun _ _
        (numberFieldSpreadAdelePointTopology K M.exceptional
          (lowerModel K L S T X n j M) _ (lowerGenericFiberIso K L S T X n j M))
        (numberFieldSpreadAdelePointTopology L
          (numberFieldExceptionalPreimage (L := L) M.exceptional) M.geometric.asOver _
          (upperGenericFiberIso K L S T X n j M))
        (adelicPointHomeomorph K L S T X n j M)

/-- Changing the specified spreads preserves the entire underlying comparison map. -/
@[simp]
theorem adelicPointHomeomorphOfSpreads_apply
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
      adelicPointHomeomorph K L S T X n j M p := rfl

end Langlands.Global.NumberFieldProjectiveWeilAdeleHomeomorph
