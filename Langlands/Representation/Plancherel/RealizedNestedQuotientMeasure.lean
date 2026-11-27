import Langlands.Representation.Plancherel.StandardIntertwiningGroupTransport
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation
import Langlands.Representation.Aubert.General.RealizedLeviStages
import Langlands.Analysis.Local.QuotientInvariantComparison

/-! # Quotient measures of intertwiners nested through a represented Levi -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation DynamicOppositeCanonicalScalar
open QuotientIntegration

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G L : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  (o : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (Dynamic.centralizer o).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (x y : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (a b : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hx : Dynamic.parabolic x = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic a) ∧
    Dynamic.centralizer x = (Dynamic.centralizer a).map j ∧
    Dynamic.unipotent x = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent a))
  (hy : Dynamic.parabolic y = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic b) ∧
    Dynamic.centralizer y = (Dynamic.centralizer b).map j ∧
    Dynamic.unipotent y = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent b))

local notation "pt" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
local notation "d" => decomposition o
local notation "Lg" => levi o
local notation "Uₐ" => radical a
local notation "Uᵦ" => radical b
local notation "Ux" => (radical x).subgroupOf Lg
local notation "Uy" => (radical y).subgroupOf Lg
local notation "QG" => QuotientSpace (U := radical x) (radical y)
local notation "Qlit" => QuotientSpace (U := Ux) Uy
local notation "QL" => QuotientSpace (U := Uₐ) Uᵦ
local notation "hxU" => Dynamic.unipotent_le_realized o j hj a x hx.2.2 pt
local notation "hyU" => Dynamic.unipotent_le_realized o j hj b y hy.2.2 pt
local notation "hyP" => (decomposition y).unipotent_le.trans
  (Dynamic.realized_parabolic_le o j hj b y hy.1 pt)
local notation "ep" => nestedRadicalQuotientHomeomorph d hyP hxU hyU (projection_continuous o)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom] in
private theorem realizedRadical_symm_mem (s : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (t : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
    (ht : Dynamic.parabolic s = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic t) ∧
      Dynamic.centralizer s = (Dynamic.centralizer t).map j ∧
      Dynamic.unipotent s = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent t))
    (v : Lg) : v ∈ (radical s).subgroupOf Lg ↔ (e).symm v ∈ radical t := by
  have hs := RealizedLeviTransport.unipotent_mem F o j hj hjc t s ht ((e).symm v)
  change (e).symm v ∈ radical t ↔ (e) ((e).symm v) ∈ (radical s).subgroupOf Lg at hs
  rw [(e).apply_symm_apply] at hs
  exact hs.symm

local notation "ea" => realizedRadical_symm_mem o j hj hjc x a hx
local notation "eb" => realizedRadical_symm_mem o j hj hjc y b hy
local notation "er" => ambientEquivQuotient (e).symm ea eb

/-- Project the ambient target radical to the outer Levi and transport its
quotient to the rational points of the represented Levi scheme. -/
def realizedNestedQuotientHomeomorph : QG ≃ₜ QL := (ep).trans er

local notation "E" => realizedNestedQuotientHomeomorph o j hj hjc x y a b hx hy

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom] in
/-- In the inverse quotient chart an inner radical element is represented by
its image in the ambient target radical. -/
theorem realizedNestedQuotientHomeomorph_symm_mk (v : Uᵦ) :
    (E).symm (Quotient.mk _ v) =
      Quotient.mk _ (nestedTargetRadicalSection
        ((GroupTransport.subgroupEquiv (e).symm eb).symm v)) := by
  change (ep).symm ((er).symm (Quotient.mk _ v)) = _
  rw [ambientEquivQuotient_symm_mk, nestedRadicalQuotientHomeomorph_symm_mk]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom] in
/-- Every inner target radical point gives an ambient target radical
representative with its exact outer-Levi image. -/
theorem exists_realizedNestedQuotient_representative (v : Uᵦ) :
    ∃ w : radical y, (w : rationalPoints G) = (e (v : rationalPoints L) : rationalPoints G) ∧
      (E).symm (Quotient.mk _ v) = Quotient.mk _ w := by
  refine ⟨_, rfl, realizedNestedQuotientHomeomorph_symm_mk o j hj hjc x y a b hx hy v⟩

local instance literalQuotientMeasurable : MeasurableSpace Qlit := borel _
local instance literalQuotientBorel : BorelSpace Qlit := ⟨rfl⟩

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))

local notation "qG" => pairQuotientMeasure K hK x y
local notation "qL" => pairQuotientMeasure K' hK' a b
local notation "S" => (Uₐ).subgroupOf Uᵦ

set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient and inner source-normalized quotient measures differ by one
fixed positive factor after the explicit quotient comparison. -/
theorem exists_realizedNestedQuotientMeasure_eq_smul :
    ∃ c : ℝ≥0, 0 < c ∧ (qG).map E = c • qL := by
  let hGq := pairQuotientMeasure_isCompatible K hK x y
  let hLq := pairQuotientMeasure_isCompatible K' hK' a b
  let : (qG).Regular := hGq.regular
  let : (qL).Regular := hLq.regular
  let N : Measure QL := (qG).map E
  let : N.Regular := Measure.Regular.map E
  have hN : N ≠ 0 := by
    intro hzero
    have hid : (E).symm ∘ (E : QG → QL) = id := funext (E).symm_apply_apply
    have he : N.map (E).symm = qG :=
      (Measure.map_map (E).symm.continuous.measurable (E).continuous.measurable).trans
        (by rw [hid, Measure.map_id])
    rw [hzero, Measure.map_zero] at he
    exact hGq.nonzero he.symm
  have hright (v : Uᵦ) : MeasurePreserving (rightTranslate S v) N N := by
    have hNmap : N = ((qG).map ep).map er :=
      (Measure.map_map (er).continuous.measurable (ep).continuous.measurable).symm
    rw [hNmap]
    exact ambientEquivQuotient_map_right_invariant (e).symm ea eb ((qG).map ep)
      (fun w => nestedRadicalQuotientHomeomorph_map_right_invariant d hyP hxU hyU
        (projection_continuous o) qG hGq.right_invariant w) v
  have hS : IsClosed (S : Set Uᵦ) := (radical_isClosed a).preimage continuous_subtype_val
  let : LocallyCompactSpace Uᵦ := (radical_isClosed b).locallyCompactSpace
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  obtain ⟨c, hc, he⟩ := exists_pos_smul_eq_of_rightInvariant_quotient S hS
    (pairIntersectionHaar K' hK' a b) N qL hN hLq.nonzero hright hLq.right_invariant
  refine ⟨c.toNNReal, Real.toNNReal_pos.mpr hc, ?_⟩
  simpa only [ENNReal.ofReal, ← ENNReal.smul_def] using he

end Langlands.Plancherel.StandardIntertwining
