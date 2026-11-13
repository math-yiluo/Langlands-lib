import Langlands.Shimura.PEL.HarrisTaylorCMScaledLevels
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSystem
import Langlands.Shimura.PEL.HarrisTaylorCMTransporterEtale
import Langlands.Shimura.PEL.HarrisTaylorCMLevelCosets
import Langlands.Shimura.Coefficients.EtaleAssociatedTransport
import Langlands.Shimura.LevelHecke
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCommonRefinement

/-! # Transport data for Harris's coefficient systems along CM transporters

For a morphism of scaled CM levels (a transporter with an admissible exponent) and torsion
stages `k' ≤ k`, this file builds the transport datum from the stage-`k` coefficient sheaf of
the target level to the stage-`k'` coefficient sheaf of the source level, over the CM schemes
over the reflex field. The common cover is the normal torsor of an intersection level. The
transport maps satisfy the identity and composition laws, and assemble into a coefficient
diagram for etale restriction over scaled levels and stages.
See `HarrisTaylorCMLevelTransport.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

/-! ## Conjugation by a transporter -/

/-- Conjugation `v ↦ a⁻¹ v a` by the translating element `a` of a transporter `b : V ⟶ U`,
from the group of `V` to the group of `U`. -/
def smallCMTransporterConj {V U : SmallCMLevel D} (b : V ⟶ U) :
    V.obj.subgroup →* U.obj.subgroup where
  toFun v := ⟨b.hom.element⁻¹ * v * b.hom.element, b.hom.respects v v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMTransporterConj_coe {V U : SmallCMLevel D} (b : V ⟶ U)
    (v : V.obj.subgroup) :
    (smallCMTransporterConj D b v : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) =
      b.hom.element⁻¹ * v * b.hom.element := rfl

/-- The induced map of residual groups, for normal subgroups `V' ≤ V` and `U' ≤ U` with
`a⁻¹ V' a ⊆ U'`. -/
def smallCMTransporterResidualMap {V U : SmallCMLevel D} (b : V ⟶ U) (V' U' : SmallCMLevel D)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (h : ∀ x ∈ V'.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    SmallCMResidualGroup D V V' →* SmallCMResidualGroup D U U' :=
  QuotientGroup.map _ _ (smallCMTransporterConj D b) (fun x hx => h x hx)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMTransporterResidualMap_mk {V U : SmallCMLevel D} (b : V ⟶ U)
    (V' U' : SmallCMLevel D)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (h : ∀ x ∈ V'.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup)
    (v : V.obj.subgroup) :
    smallCMTransporterResidualMap D b V' U' h (QuotientGroup.mk v) =
      QuotientGroup.mk (smallCMTransporterConj D b v) := rfl

/-- The transporter `T ⟶ U'` with the same translating element as `b : V ⟶ U`, for a level
`T` with `a⁻¹ T a ⊆ U'`. -/
def smallCMTransporterRestrict {V U : SmallCMLevel D} (b : V ⟶ U) (T U' : SmallCMLevel D)
    (h : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    T ⟶ U' :=
  ObjectProperty.homMk ⟨b.hom.element, h⟩

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem smallCMTransporterRestrict_element {V U : SmallCMLevel D} (b : V ⟶ U)
    (T U' : SmallCMLevel D)
    (h : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    (smallCMTransporterRestrict D b T U' h).hom.element = b.hom.element := rfl

/-- Two maps into the base change of an etale object agree once their first projections agree;
the second projections agree since both maps are over the base. -/
theorem etaleObjectPullback_hom_ext {X Z : Scheme.{0}} (φ : Z ⟶ X) {P : Z.Etale} {B : X.Etale}
    {f g : P ⟶ (etaleObjectPullback φ).obj B}
    (hfg : f.left ≫ pullback.fst B.hom φ = g.left ≫ pullback.fst B.hom φ) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext hfg
  have hf : f.left ≫ pullback.snd B.hom φ = P.hom := Over.w f.toCommaMorphism
  have hg : g.left ≫ pullback.snd B.hom φ = P.hom := Over.w g.toCommaMorphism
  rw [hf, hg]

/-- The underlying morphism of the comparison of base change along a composite is the comparison
of the base changes of the underlying etale object. -/
theorem etaleTorsorPullbackCompMap_left {X Z V : Scheme.{0}} (f : Z ⟶ X) (g : V ⟶ Z)
    {G : Type} [Group G] (Y : Action X.Etale G) :
    (etaleTorsorPullbackCompMap f g Y).left = ((etaleObjectPullbackComp f g).hom.app Y.V).left := by
  simp [etaleTorsorPullbackCompMap, etaleTorsorPullbackComp, etaleObjectPullbackComp]

@[reassoc] theorem etaleTorsorPullbackCompMap_fst_fst {X Z V : Scheme.{0}} (f : Z ⟶ X)
    (g : V ⟶ Z) {G : Type} [Group G] (Y : Action X.Etale G) :
    (etaleTorsorPullbackCompMap f g Y).left ≫
        pullback.fst ((etaleTorsorPullbackFunctor f G).obj Y).V.hom g ≫
        pullback.fst Y.V.hom f = pullback.fst Y.V.hom (g ≫ f) := by
  rw [etaleTorsorPullbackCompMap_left]
  exact etaleObjectPullbackComp_hom_fst_fst f g Y.V

@[reassoc] theorem etaleTorsorPullbackCompMap_fst_snd {X Z V : Scheme.{0}} (f : Z ⟶ X)
    (g : V ⟶ Z) {G : Type} [Group G] (Y : Action X.Etale G) :
    (etaleTorsorPullbackCompMap f g Y).left ≫
        pullback.fst ((etaleTorsorPullbackFunctor f G).obj Y).V.hom g ≫
        pullback.snd Y.V.hom f = pullback.snd Y.V.hom (g ≫ f) ≫ g := by
  rw [etaleTorsorPullbackCompMap_left]
  exact etaleObjectPullbackComp_hom_fst_snd f g Y.V

/-! ## Transport data between normal CM torsors -/

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

set_option quotPrecheck false in
local notation "normalTorsor" U:max V:max hVU:max => cmNormalGeometricTorsor_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor U V hVU q
  existence geometry (hRigid U) DominantUnramifiedEtaleProof.dominantUnramifiedEtale

/-- The transporter `T ⟶ U'` and the inclusion `T ≤ V` followed by `b` agree after the
inclusion `U' ≤ U`. -/
theorem cmSchemeTower_transporterRestrict_comm {V U : SmallCMLevel D} (b : V ⟶ U)
    (T U' : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    (schemes).map (smallCMTransporterRestrict D b T U' hTU') ≫
        (schemes).map (smallCMInclusion D hU') =
      (schemes).map (smallCMInclusion D hT) ≫ (schemes).map b := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  change b.hom.element * 1 = 1 * b.hom.element
  simp

/-- The map from the normal torsor of `T ≤ V` to the base change along `φ` of the normal torsor
of `U' ≤ U`, induced by the transporter `T ⟶ U'` and the inclusion `T ≤ V`. -/
def cmNormalTransportToSource {V U : SmallCMLevel D} (b : V ⟶ U)
    (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b)
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    (normalTorsor V T hT).val.V ⟶ ((etaleTorsorPullbackFunctor φ
      (SmallCMResidualGroup D U U')).obj (normalTorsor U U' hU').val).V :=
  MorphismProperty.Over.homMk
    (pullback.lift ((schemes).map (smallCMTransporterRestrict D b T U' hTU'))
      ((schemes).map (smallCMInclusion D hT)) (by
        rw [hφ]
        exact cmSchemeTower_transporterRestrict_comm D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q b T U' hT hU' hTU'))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)] theorem cmNormalTransportToSource_fst {V U : SmallCMLevel D}
    (b : V ⟶ U) (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b)
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    (cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid b φ hφ U' hU' T
        hT hTU').left ≫ pullback.fst _ _ =
      (schemes).map (smallCMTransporterRestrict D b T U' hTU') :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmNormalTransportToSource_snd {V U : SmallCMLevel D}
    (b : V ⟶ U) (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b)
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup) :
    (cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid b φ hφ U' hU' T
        hT hTU').left ≫ pullback.snd _ _ =
      (schemes).map (smallCMInclusion D hT) :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
/-- The source maps of composable transporters compose: the source map of `bb` followed by the
base change of the source map of `ba` is the source map of `bb ≫ ba` followed by the comparison
of iterated base change. -/
theorem cmNormalTransportToSource_comp {X Y Z : SmallCMLevel D} (bb : X ⟶ Y) (ba : Y ⟶ Z)
    (φb : (schemes).obj X ⟶ (schemes).obj Y) (hφb : φb = (schemes).map bb)
    (φa : (schemes).obj Y ⟶ (schemes).obj Z) (hφa : φa = (schemes).map ba)
    (hφab : φb ≫ φa = (schemes).map (bb ≫ ba))
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ Z.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf Z.obj.subgroup).Normal]
    (Ta : SmallCMLevel D) (hTa : Ta.obj.subgroup ≤ Y.obj.subgroup)
    [(Ta.obj.subgroup.subgroupOf Y.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ X.obj.subgroup)
    [(T.obj.subgroup.subgroupOf X.obj.subgroup).Normal]
    (h₁ : ∀ x ∈ T.obj.subgroup, bb.hom.element⁻¹ * x * bb.hom.element ∈ Ta.obj.subgroup)
    (h₂ : ∀ x ∈ Ta.obj.subgroup, ba.hom.element⁻¹ * x * ba.hom.element ∈ U'.obj.subgroup)
    (h₃ : ∀ x ∈ T.obj.subgroup,
      (bb ≫ ba).hom.element⁻¹ * x * (bb ≫ ba).hom.element ∈ U'.obj.subgroup) :
    cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid bb φb hφb Ta hTa
        T hT h₁ ≫
      etaleCoverMapPullback φb
        (cmNormalTransportToSource D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid ba φa hφa U' hU'
          Ta hTa h₂) =
    cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid (bb ≫ ba)
        (φb ≫ φa) hφab U' hU' T hT h₃ ≫
      etaleTorsorPullbackCompMap φa φb (normalTorsor Z U' hU').val := by
  apply etaleObjectPullback_hom_ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      etaleTorsorPullbackCompMap_fst_fst]
    unfold etaleCoverMapPullback
    rw [etaleObjectPullback_map_fst_assoc, cmNormalTransportToSource_fst_assoc,
      cmNormalTransportToSource_fst, cmNormalTransportToSource_fst,
      ← CategoryTheory.Functor.map_comp]
    congr 1
  · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      etaleTorsorPullbackCompMap_fst_snd]
    unfold etaleCoverMapPullback
    rw [etaleObjectPullback_map_fst_assoc, cmNormalTransportToSource_fst_assoc,
      cmNormalTransportToSource_snd, cmNormalTransportToSource_snd_assoc, hφb,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    apply CompactOpenLevel.Arrow.ext
    change bb.hom.element * 1 = 1 * bb.hom.element
    simp

variable {K : Type} [Field K] [NumberField K] (p : Global.FinitePlace ℚ)

local notation "Rcoeff" => HarrisCoefficientIntegers K p

/-- The transport datum along a transporter `b : V ⟶ U` of small CM levels, from the normal
torsor of `U' ≤ U` with coefficients `M` to the normal torsor of `V' ≤ V` with coefficients
`M'`. The common cover is the normal torsor of a level `T ≤ V' ≤ V` with `a⁻¹ T a ⊆ U'`. Its
map to the base change of the source torsor is induced by the transporter `T ⟶ U'` and the
inclusion `T ≤ V`, its map to the target torsor by the inclusion `T ≤ V'`, and the coefficient
map is `c`. The scheme map `φ` is the tower map of `b`, kept as a separate argument. -/
def cmNormalTransportDatum {V U : SmallCMLevel D} (b : V ⟶ U)
    (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b)
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (V' : SmallCMLevel D) (hV' : V'.obj.subgroup ≤ V.obj.subgroup)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ V'.obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup)
    (M : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U U'))
    (M' : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D V V'))
    (c : M.V ⟶ M'.V)
    (hc : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c = c ≫ M'.ρ (QuotientGroup.mk v)) :
    EtaleTransportDatum (R := Rcoeff) φ (normalTorsor U U' hU').val (normalTorsor V V' hV').val
      M M' where
  group := SmallCMResidualGroup D V T
  toSourceGroup := smallCMTransporterResidualMap D b T U' hTU'
  toTargetGroup := smallCMResidualQuotientMap D V V' T hTV'
  cover := (normalTorsor V T hT).val
  isFiniteGeometricTorsor := (normalTorsor V T hT).property
  toSource := cmNormalTransportToSource D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q existence geometry hRigid b φ hφ U' hU' T hT hTU'
  toSource_comm := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H v =>
      apply MorphismProperty.Over.Hom.ext
      rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
      apply pullback.hom_ext
      · rw [Category.assoc, cmNormalTransportToSource_fst, Category.assoc]
        erw [etaleObjectPullback_map_fst]
        rw [cmNormalTransportToSource_fst_assoc]
        change (schemes).map (smallCMNormalInverseArrow D V T hT v) ≫
            (schemes).map (smallCMTransporterRestrict D b T U' hTU') =
          (schemes).map (smallCMTransporterRestrict D b T U' hTU') ≫
            (schemes).map (smallCMNormalInverseArrow D U U' hU' (smallCMTransporterConj D b v))
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply ObjectProperty.hom_ext
        apply CompactOpenLevel.Arrow.ext
        change (v : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ * b.hom.element =
          b.hom.element * (b.hom.element⁻¹ * v * b.hom.element)⁻¹
        group
      · rw [Category.assoc, cmNormalTransportToSource_snd, Category.assoc]
        erw [etaleObjectPullback_map_snd]
        rw [cmNormalTransportToSource_snd]
        exact ((normalTorsor V T hT).val.ρ (QuotientGroup.mk v)).w
  toTarget := MorphismProperty.Over.homMk ((schemes).map (smallCMInclusion D hTV')) (by
    change (schemes).map (smallCMInclusion D hTV') ≫ (schemes).map (smallCMInclusion D hV') =
      (schemes).map (smallCMInclusion D hT)
    rw [← Functor.map_comp, smallCMInclusion_trans])
  toTarget_comm := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H v =>
      apply MorphismProperty.Over.Hom.ext
      change (schemes).map (smallCMNormalInverseArrow D V T hT v) ≫
          (schemes).map (smallCMInclusion D hTV') =
        (schemes).map (smallCMInclusion D hTV') ≫
          (schemes).map (smallCMNormalInverseArrow D V V' hV' v)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply ObjectProperty.hom_ext
      apply CompactOpenLevel.Arrow.ext
      change (v : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ * 1 =
        1 * (v : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹
      simp
  coefficient := c
  coefficient_comm := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H v => exact hc v

/-! ## Transport data for Harris's coefficient systems -/

variable [Module.Finite ℚ A]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)

local notation "ℓ" => harrisCoefficientPrime p
local notation "hℓ" => harrisCoefficientPrime_ne_zero p
local notation "coeffLevel" U:max k:max => cmHarrisCoefficientLevel D ρ p U ℓ hℓ k

/-- The standard common level for a morphism `f : X ⟶ Y` of scaled levels and stages `k' ≤ k`:
the elements `x` of the stage-`k'` coefficient level of `X` with `a⁻¹ x a` in the stage-`k`
coefficient level of `Y`, where `a` is the translating element of `f`. -/
def cmScaledTransportLevel {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ) :
    SmallCMLevel D :=
  smallCMHeckeLevel D (coeffLevel X.level k') (coeffLevel Y.level k)
    (CMScaledLevel.Hom.hom f).hom.element

omit [IsCMField F] [IsScalarTower E F A] in
theorem mem_cmScaledTransportLevel {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ)
    (x : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    x ∈ (cmScaledTransportLevel D p ρ f k' k).obj.subgroup ↔
      x ∈ (coeffLevel X.level k').obj.subgroup ∧
        (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x * (CMScaledLevel.Hom.hom f).hom.element ∈
          (coeffLevel Y.level k).obj.subgroup :=
  Langlands.Shimura.LevelHecke.mem_heckeLevel

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledTransportLevel_le_coeff {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ) :
    (cmScaledTransportLevel D p ρ f k' k).obj.subgroup ≤ (coeffLevel X.level k').obj.subgroup :=
  fun x hx => ((mem_cmScaledTransportLevel D p ρ f k' k x).1 hx).1

theorem cmScaledTransportLevel_le {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ) :
    (cmScaledTransportLevel D p ρ f k' k).obj.subgroup ≤ X.level.obj.subgroup :=
  (cmScaledTransportLevel_le_coeff D p ρ f k' k).trans
    (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledTransportLevel_conj {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ) :
    ∀ x ∈ (cmScaledTransportLevel D p ρ f k' k).obj.subgroup,
      (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x * (CMScaledLevel.Hom.hom f).hom.element ∈
        (coeffLevel Y.level k).obj.subgroup :=
  fun x hx => ((mem_cmScaledTransportLevel D p ρ f k' k x).1 hx).2

instance cmScaledTransportLevel_normal {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k' k : ℕ) :
    ((cmScaledTransportLevel D p ρ f k' k).obj.subgroup.subgroupOf
      X.level.obj.subgroup).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [mem_cmScaledTransportLevel] at hn ⊢
  obtain ⟨hn1, hn2⟩ := hn
  set a := (CMScaledLevel.Hom.hom f).hom.element
  refine ⟨?_, ?_⟩
  · have hX := (cmHarrisCoefficientLevel_normal D ρ p X.level ℓ hℓ k').conj_mem
      ⟨n, cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k' hn1⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hn1) g
    rw [Subgroup.mem_subgroupOf] at hX
    simpa using hX
  · have hg : a⁻¹ * (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) * a ∈ Y.level.obj.subgroup :=
      (CMScaledLevel.Hom.hom f).hom.respects g g.2
    have hY := (cmHarrisCoefficientLevel_normal D ρ p Y.level ℓ hℓ k).conj_mem
      ⟨a⁻¹ * n * a, cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k hn2⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hn2) ⟨_, hg⟩
    rw [Subgroup.mem_subgroupOf] at hY
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hY ⊢
    have e : a⁻¹ * ((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) * (n : _) *
        ((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ))⁻¹) * a =
        (a⁻¹ * g * a) * (a⁻¹ * n * a) * (a⁻¹ * g * a)⁻¹ := by group
    rw [e]
    exact hY

local notation "transportDatum" => cmNormalTransportDatum D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p
local notation "coefficients" U:max => cmHarrisCoefficientDiagram D ρ p U ℓ hℓ

/-- The transport datum of Harris's coefficient systems for a morphism `f : X ⟶ Y` of scaled
levels and stages `k' ≤ k`, with a common level `T` of the level of `X`: from stage `k` at the
level of `Y` to stage `k'` at the level of `X`, with coefficient map
`cmHarrisTorsionTransport f`. -/
def cmHarrisTransportDatumAt {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k' k : ℕ} (hk : k' ≤ k)
    (φ : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f))
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ X.level.obj.subgroup)
    [(T.obj.subgroup.subgroupOf X.level.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ (coeffLevel X.level k').obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x *
      (CMScaledLevel.Hom.hom f).hom.element ∈ (coeffLevel Y.level k).obj.subgroup) :=
  transportDatum (CMScaledLevel.Hom.hom f) φ hφ (coeffLevel Y.level k)
    (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k) (coeffLevel X.level k')
    (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k') T hT hTV' hTU'
    ((coefficients Y.level).action (op k)) ((coefficients X.level).action (op k'))
    (cmHarrisTorsionTransport D ρ p f hk)
    (fun v => cmHarrisTorsionTransport_comm D ρ p f hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom f) v) rfl)

/-- The transport datum with the standard common level `cmScaledTransportLevel`. -/
def cmHarrisTransportDatum {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k' k : ℕ} (hk : k' ≤ k)
    (φ : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) :=
  cmHarrisTransportDatumAt D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q existence geometry hRigid p ρ f hk φ hφ
    (cmScaledTransportLevel D p ρ f k' k) (cmScaledTransportLevel_le D p ρ f k' k)
    (cmScaledTransportLevel_le_coeff D p ρ f k' k) (cmScaledTransportLevel_conj D p ρ f k' k)

local notation "datumAt" => cmHarrisTransportDatumAt D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q existence geometry hRigid p ρ

/-- The transport map does not depend on the common level: for common levels `T₁ ≤ T₂` the
transport maps agree. -/
theorem cmHarrisTransportDatumAt_sheafMap_eq {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y)
    {k' k : ℕ} (hk : k' ≤ k) (φ : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) [Etale φ]
    (T₁ : SmallCMLevel D) (hT₁ : T₁.obj.subgroup ≤ X.level.obj.subgroup)
    [(T₁.obj.subgroup.subgroupOf X.level.obj.subgroup).Normal]
    (hTV'₁ : T₁.obj.subgroup ≤ (coeffLevel X.level k').obj.subgroup)
    (hTU'₁ : ∀ x ∈ T₁.obj.subgroup, (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x *
      (CMScaledLevel.Hom.hom f).hom.element ∈ (coeffLevel Y.level k).obj.subgroup)
    (T₂ : SmallCMLevel D) (hT₂ : T₂.obj.subgroup ≤ X.level.obj.subgroup)
    [(T₂.obj.subgroup.subgroupOf X.level.obj.subgroup).Normal]
    (hTV'₂ : T₂.obj.subgroup ≤ (coeffLevel X.level k').obj.subgroup)
    (hTU'₂ : ∀ x ∈ T₂.obj.subgroup, (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x *
      (CMScaledLevel.Hom.hom f).hom.element ∈ (coeffLevel Y.level k).obj.subgroup)
    (h12 : T₁.obj.subgroup ≤ T₂.obj.subgroup) :
    (datumAt f hk φ hφ T₁ hT₁ hTV'₁ hTU'₁).sheafMap
        (normalTorsor X.level (coeffLevel X.level k')
          (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')).property =
      (datumAt f hk φ hφ T₂ hT₂ hTV'₂ hTU'₂).sheafMap
        (normalTorsor X.level (coeffLevel X.level k')
          (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')).property := by
  refine EtaleTransportDatum.sheafMap_eq_of_refines _ _ _
    (MorphismProperty.Over.homMk ((schemes).map (smallCMInclusion D h12)) (by
      change (schemes).map (smallCMInclusion D h12) ≫ (schemes).map (smallCMInclusion D hT₂) =
        (schemes).map (smallCMInclusion D hT₁)
      rw [← Functor.map_comp, smallCMInclusion_trans])) ?_ ?_ rfl
  · apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    apply pullback.hom_ext
    · change (schemes).map (smallCMInclusion D h12) ≫ (cmNormalTransportToSource D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q existence
          geometry hRigid _ φ hφ _ _ T₂ hT₂ hTU'₂).left ≫ pullback.fst _ _ =
        (cmNormalTransportToSource D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid _ φ hφ _ _ T₁
          hT₁ hTU'₁).left ≫ pullback.fst _ _
      rw [cmNormalTransportToSource_fst, cmNormalTransportToSource_fst, ← Functor.map_comp]
      congr 1
      apply ObjectProperty.hom_ext
      apply CompactOpenLevel.Arrow.ext
      change 1 * _ = _
      exact one_mul _
    · change (schemes).map (smallCMInclusion D h12) ≫ (cmNormalTransportToSource D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q existence
          geometry hRigid _ φ hφ _ _ T₂ hT₂ hTU'₂).left ≫ pullback.snd _ _ =
        (cmNormalTransportToSource D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid _ φ hφ _ _ T₁
          hT₁ hTU'₁).left ≫ pullback.snd _ _
      rw [cmNormalTransportToSource_snd, cmNormalTransportToSource_snd, ← Functor.map_comp,
        smallCMInclusion_trans]
  · apply MorphismProperty.Over.Hom.ext
    change (schemes).map (smallCMInclusion D h12) ≫ (schemes).map (smallCMInclusion D hTV'₂) =
      (schemes).map (smallCMInclusion D hTV'₁)
    rw [← Functor.map_comp, smallCMInclusion_trans]

/-- Transport along equal scheme maps. -/
theorem cmHarrisTransportDatumAt_sheafMap_congr {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y)
    {k' k : ℕ} (hk : k' ≤ k) {φ₁ φ₂ : (schemes).obj X.level ⟶ (schemes).obj Y.level}
    (e : φ₁ = φ₂) (hφ₁ : φ₁ = (schemes).map (CMScaledLevel.Hom.hom f))
    (hφ₂ : φ₂ = (schemes).map (CMScaledLevel.Hom.hom f)) [Etale φ₁] [Etale φ₂]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ X.level.obj.subgroup)
    [(T.obj.subgroup.subgroupOf X.level.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ (coeffLevel X.level k').obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x *
      (CMScaledLevel.Hom.hom f).hom.element ∈ (coeffLevel Y.level k).obj.subgroup) :
    (EtalePullback.restrictionCongr Rcoeff e).hom.app _ ≫
        (datumAt f hk φ₂ hφ₂ T hT hTV' hTU').sheafMap
          (normalTorsor X.level (coeffLevel X.level k')
            (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')).property =
      (datumAt f hk φ₁ hφ₁ T hT hTV' hTU').sheafMap
          (normalTorsor X.level (coeffLevel X.level k')
            (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')).property := by
  subst e
  simp [EtalePullback.restrictionCongr]

/-! ## The transport maps and their identity law -/

local notation "standardDatum" => cmHarrisTransportDatum D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ

/-- The transport map of Harris's coefficient systems for a morphism `f : X ⟶ Y` of scaled
levels and stages `k' ≤ k`, along an etale scheme map `φ` equal to the tower map of `f`: from
the restriction along `φ` of the stage-`k` coefficient sheaf at the level of `Y` to the
stage-`k'` coefficient sheaf at the level of `X`. -/
def cmHarrisTransportSheafMap {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) {k' k : ℕ} (hk : k' ≤ k)
    (φ : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) [Etale φ] :=
  (standardDatum f hk φ hφ).sheafMap
    (normalTorsor X.level (coeffLevel X.level k')
      (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')).property

local notation "transportMap" => cmHarrisTransportSheafMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ

/-- Identity law: for an identity of scaled levels and equal stages, along a scheme map equal to
the identity, the transport map is the identification of the restriction along the identity. -/
theorem cmHarrisTransportSheafMap_id (Y : CMScaledLevel D ρ p) (k : ℕ)
    (φ : (schemes).obj Y.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom (𝟙 Y))) [Etale φ] (e : φ = 𝟙 _) :
    transportMap (𝟙 Y) (le_refl k) φ hφ =
      (EtalePullback.restrictionCongr Rcoeff e).hom.app _ ≫
        (EtalePullback.restrictionId (ModuleCat.{0} Rcoeff)).hom.app _ := by
  have hφ₂ : 𝟙 ((schemes).obj Y.level) = (schemes).map (CMScaledLevel.Hom.hom (𝟙 Y)) :=
    (CategoryTheory.Functor.map_id _ _).symm
  have hcongr := cmHarrisTransportDatumAt_sheafMap_congr D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
    (𝟙 Y) (le_refl k) e hφ hφ₂ (cmScaledTransportLevel D p ρ (𝟙 Y) k k)
    (cmScaledTransportLevel_le D p ρ (𝟙 Y) k k) (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k k)
    (cmScaledTransportLevel_conj D p ρ (𝟙 Y) k k)
  have hid := EtaleTransportDatum.sheafMap_id
    (datumAt (𝟙 Y) (le_refl k) (𝟙 _) hφ₂ (cmScaledTransportLevel D p ρ (𝟙 Y) k k)
      (cmScaledTransportLevel_le D p ρ (𝟙 Y) k k)
      (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k k)
      (cmScaledTransportLevel_conj D p ρ (𝟙 Y) k k))
    (normalTorsor Y.level (coeffLevel Y.level k)
      (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k)).property ?_ ?_
  · exact hcongr.symm.trans (by rw [hid])
  · apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    change (cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid _ _ hφ₂ _ _ _ _ _
        ).left ≫ pullback.fst _ _ = _
    rw [cmNormalTransportToSource_fst]
    change _ = (schemes).map (smallCMInclusion D _)
    congr 1
  · change cmHarrisTorsionTransport D ρ p (𝟙 Y) (le_refl k) = 𝟙 _
    rw [cmHarrisTorsionTransport_id]
    change ((cmHarrisTorsionSystem D ρ p Y.level ℓ).map (𝟙 (op k))).hom = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl

/-! ## The common level for a composite -/

/-- The common level for composable morphisms `fb : X ⟶ Y` and `fa : Y ⟶ Z` of scaled levels
and stages `k'' ≤ k' ≤ k`: the elements `x` of the standard common level of `fb` with
`b⁻¹ x b` in the standard common level of `fa`, where `b` is the translating element of
`fb`. -/
def cmScaledCompositeLevel {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y) (fa : Y ⟶ Z)
    (k'' k' k : ℕ) : SmallCMLevel D :=
  smallCMCommonLevel D (cmScaledTransportLevel D p ρ fb k'' k')
    (smallCMHeckeLevel D X.level (cmScaledTransportLevel D p ρ fa k' k)
      (CMScaledLevel.Hom.hom fb).hom.element)

omit [IsCMField F] [IsScalarTower E F A] in
theorem mem_cmScaledCompositeLevel {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y) (fa : Y ⟶ Z)
    (k'' k' k : ℕ) (x : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    x ∈ (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup ↔
      x ∈ (cmScaledTransportLevel D p ρ fb k'' k').obj.subgroup ∧
        (x ∈ X.level.obj.subgroup ∧
          (CMScaledLevel.Hom.hom fb).hom.element⁻¹ * x * (CMScaledLevel.Hom.hom fb).hom.element ∈
            (cmScaledTransportLevel D p ρ fa k' k).obj.subgroup) := by
  unfold cmScaledCompositeLevel
  rw [smallCMCommonLevel_subgroup, Subgroup.mem_inf]
  exact and_congr Iff.rfl Langlands.Shimura.LevelHecke.mem_heckeLevel

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledCompositeLevel_le_transport {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup ≤
      (cmScaledTransportLevel D p ρ fb k'' k').obj.subgroup :=
  fun x hx => ((mem_cmScaledCompositeLevel D p ρ fb fa k'' k' k x).1 hx).1

theorem cmScaledCompositeLevel_le {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup ≤ X.level.obj.subgroup :=
  (cmScaledCompositeLevel_le_transport D p ρ fb fa k'' k' k).trans
    (cmScaledTransportLevel_le D p ρ fb k'' k')

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledCompositeLevel_le_coeff {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup ≤
      (coeffLevel X.level k'').obj.subgroup :=
  (cmScaledCompositeLevel_le_transport D p ρ fb fa k'' k' k).trans
    (cmScaledTransportLevel_le_coeff D p ρ fb k'' k')

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledCompositeLevel_conj_transport {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    ∀ x ∈ (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup,
      (CMScaledLevel.Hom.hom fb).hom.element⁻¹ * x * (CMScaledLevel.Hom.hom fb).hom.element ∈
        (cmScaledTransportLevel D p ρ fa k' k).obj.subgroup :=
  fun x hx => ((mem_cmScaledCompositeLevel D p ρ fb fa k'' k' k x).1 hx).2.2

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledCompositeLevel_conj {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    ∀ x ∈ (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup,
      (CMScaledLevel.Hom.hom (fb ≫ fa)).hom.element⁻¹ * x *
        (CMScaledLevel.Hom.hom (fb ≫ fa)).hom.element ∈ (coeffLevel Z.level k).obj.subgroup := by
  intro x hx
  have h1 := cmScaledTransportLevel_conj D p ρ fa k' k _
    (cmScaledCompositeLevel_conj_transport D p ρ fb fa k'' k' k x hx)
  have e : (CMScaledLevel.Hom.hom (fb ≫ fa)).hom.element =
      (CMScaledLevel.Hom.hom fb).hom.element * (CMScaledLevel.Hom.hom fa).hom.element := rfl
  rw [e]
  convert h1 using 1
  group

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmScaledCompositeLevel_le_standard {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    (cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup ≤
      (cmScaledTransportLevel D p ρ (fb ≫ fa) k'' k).obj.subgroup := by
  intro x hx
  rw [mem_cmScaledTransportLevel]
  exact ⟨cmScaledCompositeLevel_le_coeff D p ρ fb fa k'' k' k hx,
    cmScaledCompositeLevel_conj D p ρ fb fa k'' k' k x hx⟩

instance cmScaledCompositeLevel_normal {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) (k'' k' k : ℕ) :
    ((cmScaledCompositeLevel D p ρ fb fa k'' k' k).obj.subgroup.subgroupOf
      X.level.obj.subgroup).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, mem_cmScaledCompositeLevel] at hn ⊢
  obtain ⟨hn1, -, hn3⟩ := hn
  set b := (CMScaledLevel.Hom.hom fb).hom.element
  refine ⟨?_, (X.level.obj.subgroup.mul_mem (X.level.obj.subgroup.mul_mem g.2
    (cmScaledTransportLevel_le D p ρ fb k'' k' hn1)) (X.level.obj.subgroup.inv_mem g.2)), ?_⟩
  · have hX := (cmScaledTransportLevel_normal D p ρ fb k'' k').conj_mem
      ⟨n, cmScaledTransportLevel_le D p ρ fb k'' k' hn1⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hn1) g
    rw [Subgroup.mem_subgroupOf] at hX
    simpa using hX
  · have hg : b⁻¹ * (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) * b ∈ Y.level.obj.subgroup :=
      (CMScaledLevel.Hom.hom fb).hom.respects g g.2
    have hY := (cmScaledTransportLevel_normal D p ρ fa k' k).conj_mem
      ⟨b⁻¹ * n * b, cmScaledTransportLevel_le D p ρ fa k' k hn3⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hn3) ⟨_, hg⟩
    rw [Subgroup.mem_subgroupOf] at hY
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hY ⊢
    have e : b⁻¹ * ((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) * (n : _) *
        ((g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ))⁻¹) * b =
        (b⁻¹ * g * b) * (b⁻¹ * n * b) * (b⁻¹ * g * b)⁻¹ := by group
    rw [e]
    exact hY

/-! ## The composition law -/

set_option quotPrecheck false in
local notation "toSourceMap" => cmNormalTransportToSource D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid

set_option maxHeartbeats 3200000 in
/-- Composition law: for composable morphisms `fb : X ⟶ Y` and `fa : Y ⟶ Z` of scaled levels and
stages `k'' ≤ k' ≤ k`, the transport map of the composite, after the identification of iterated
restriction, is the restriction of the transport map of `fa` followed by the transport map of
`fb`. -/
theorem cmHarrisTransportSheafMap_comp {X Y Z : CMScaledLevel D ρ p} (fb : X ⟶ Y)
    (fa : Y ⟶ Z) {k'' k' k : ℕ} (hk₁ : k'' ≤ k') (hk₂ : k' ≤ k)
    (φa : (schemes).obj Y.level ⟶ (schemes).obj Z.level)
    (hφa : φa = (schemes).map (CMScaledLevel.Hom.hom fa)) [Etale φa]
    (φb : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφb : φb = (schemes).map (CMScaledLevel.Hom.hom fb)) [Etale φb]
    (φab : (schemes).obj X.level ⟶ (schemes).obj Z.level)
    (hφab : φab = (schemes).map (CMScaledLevel.Hom.hom (fb ≫ fa))) [Etale φab]
    (e : φb ≫ φa = φab) :
    (EtalePullback.restrictionComp φa (ModuleCat.{0} Rcoeff) φb).hom.app _ ≫
        (EtalePullback.restrictionCongr Rcoeff e).hom.app _ ≫
        transportMap (fb ≫ fa) (hk₁.trans hk₂) φab hφab =
      (EtalePullback.restriction φb (ModuleCat.{0} Rcoeff)).map (transportMap fa hk₂ φa hφa) ≫
        transportMap fb hk₁ φb hφb := by
  have hφ₁ : φb ≫ φa = (schemes).map (CMScaledLevel.Hom.hom (fb ≫ fa)) := e.trans hφab
  have hcongr := cmHarrisTransportDatumAt_sheafMap_congr D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
    (fb ≫ fa) (hk₁.trans hk₂) e hφ₁ hφab (cmScaledTransportLevel D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_le D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_le_coeff D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_conj D p ρ (fb ≫ fa) k'' k)
  have hrefine := cmHarrisTransportDatumAt_sheafMap_eq D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
    (fb ≫ fa) (hk₁.trans hk₂) (φb ≫ φa) hφ₁ (cmScaledCompositeLevel D p ρ fb fa k'' k' k)
    (cmScaledCompositeLevel_le D p ρ fb fa k'' k' k)
    (cmScaledCompositeLevel_le_coeff D p ρ fb fa k'' k' k)
    (cmScaledCompositeLevel_conj D p ρ fb fa k'' k' k)
    (cmScaledTransportLevel D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_le D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_le_coeff D p ρ (fb ≫ fa) k'' k)
    (cmScaledTransportLevel_conj D p ρ (fb ≫ fa) k'' k)
    (cmScaledCompositeLevel_le_standard D p ρ fb fa k'' k' k)
  refine (whisker_eq _ hcongr).trans ((whisker_eq _ hrefine.symm).trans ?_)
  refine EtaleTransportDatum.sheafMap_comp φb (standardDatum fa hk₂ φa hφa)
    (standardDatum fb hk₁ φb hφb)
    (datumAt (fb ≫ fa) (hk₁.trans hk₂) (φb ≫ φa) hφ₁ (cmScaledCompositeLevel D p ρ fb fa k'' k' k)
      (cmScaledCompositeLevel_le D p ρ fb fa k'' k' k)
      (cmScaledCompositeLevel_le_coeff D p ρ fb fa k'' k' k)
      (cmScaledCompositeLevel_conj D p ρ fb fa k'' k' k)) _ _
    (toSourceMap (CMScaledLevel.Hom.hom fb) φb hφb (cmScaledTransportLevel D p ρ fa k' k)
      (cmScaledTransportLevel_le D p ρ fa k' k) (cmScaledCompositeLevel D p ρ fb fa k'' k' k)
      (cmScaledCompositeLevel_le D p ρ fb fa k'' k' k)
      (cmScaledCompositeLevel_conj_transport D p ρ fb fa k'' k' k))
    (MorphismProperty.Over.homMk ((schemes).map (smallCMInclusion D
      (cmScaledCompositeLevel_le_transport D p ρ fb fa k'' k' k))) (by
        change (schemes).map (smallCMInclusion D _) ≫ (schemes).map (smallCMInclusion D _) =
          (schemes).map (smallCMInclusion D _)
        rw [← CategoryTheory.Functor.map_comp, smallCMInclusion_trans])) ?_ ?_ ?_ ?_
  · -- the two maps to the base change of the cover of `fa`'s target agree
    dsimp only [cmHarrisTransportDatum, cmHarrisTransportDatumAt, cmNormalTransportDatum,
      etaleCoverMapPullback]
    apply etaleObjectPullback_hom_ext
    · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
      rw [Category.assoc, Category.assoc]
      erw [etaleObjectPullback_map_fst]
      rw [cmNormalTransportToSource_fst_assoc, cmNormalTransportToSource_fst]
      change (schemes).map _ ≫ (schemes).map (smallCMInclusion D _) =
        (schemes).map (smallCMInclusion D _) ≫ (schemes).map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1
      apply ObjectProperty.hom_ext
      apply CompactOpenLevel.Arrow.ext
      change (CMScaledLevel.Hom.hom fb).hom.element * 1 = 1 * (CMScaledLevel.Hom.hom fb).hom.element
      simp
  · dsimp only [cmHarrisTransportDatum, cmHarrisTransportDatumAt, cmNormalTransportDatum]
    apply MorphismProperty.Over.Hom.ext
    change (schemes).map (smallCMInclusion D _) ≫ (schemes).map (smallCMInclusion D _) =
      (schemes).map (smallCMInclusion D _)
    rw [← CategoryTheory.Functor.map_comp, smallCMInclusion_trans]
  · exact cmNormalTransportToSource_comp D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q existence geometry hRigid (CMScaledLevel.Hom.hom fb)
      (CMScaledLevel.Hom.hom fa) φb hφb φa hφa hφ₁ _ _ _ _ _ _ _ _ _
  · exact (cmHarrisTorsionTransport_comp D ρ p fb fa hk₁ hk₂).symm

/-! ## The coefficient diagram over scaled levels and stages -/

/-- Forgetting the exponent of a scaled level. -/
def cmScaledLevelForget : CMScaledLevel D ρ p ⥤ SmallCMLevel D where
  obj X := X.level
  map f := CMScaledLevel.Hom.hom f

/-- The scheme diagram of the CM tower over scaled levels and stages: the vertex `(X, k)` is the
CM scheme of the level of `X`, and a morphism `f` of scaled levels gives the tower map of its
transporter. -/
def cmScaledSchemeDiagram : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ ⥤ Scheme.{0}ᵒᵖ :=
  CategoryTheory.Prod.fst _ _ ⋙ (cmScaledLevelForget D p ρ ⋙ schemes).op

local notation "scaledSchemes" => cmScaledSchemeDiagram D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ

include existence geometry hRigid in
/-- Every transition of the scaled scheme diagram is etale. -/
theorem cmScaledSchemeDiagram_etale {i j : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ} (a : i ⟶ j) :
    Etale ((scaledSchemes).map a).unop :=
  representedCMSchemeTower_map_etale_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenCMLevelRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q) existence geometry hRigid
    DominantUnramifiedEtaleProof.dominantUnramifiedEtale (CMScaledLevel.Hom.hom a.1.unop)

set_option maxHeartbeats 3200000 in
/-- Harris's coefficient systems over the scaled levels and stages, as a coefficient diagram for
etale restriction: the vertex `(X, k)` is the stage-`k` coefficient sheaf
`cmHarrisCoefficientSystem` of the level of `X`, and the transition of a morphism is its transport
map. -/
def cmHarrisScaledCoefficientDiagram :
    @EtalePullback.CoefficientDiagram Rcoeff _ ((CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) _ (scaledSchemes)
      (fun a => cmScaledSchemeDiagram_etale D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid p ρ a) := by
  letI : ∀ {i j : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ} (a : i ⟶ j),
      Etale ((scaledSchemes).map a).unop := fun a =>
    cmScaledSchemeDiagram_etale D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q existence geometry hRigid p ρ a
  exact
    { obj := fun i => (cmHarrisCoefficientSystem D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q i.1.unop.level ρ p ℓ hℓ existence geometry
          (hRigid i.1.unop.level)).obj i.2
      map := fun {i j} a => transportMap a.1.unop (leOfHom a.2.unop)
        ((scaledSchemes).map a).unop rfl
      map_id := fun i => cmHarrisTransportSheafMap_id D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid p ρ i.1.unop
        i.2.unop ((scaledSchemes).map (𝟙 i)).unop rfl
        (congrArg Quiver.Hom.unop ((scaledSchemes).map_id i))
      map_comp := fun {i j k} a b => cmHarrisTransportSheafMap_comp D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
        p ρ b.1.unop a.1.unop (leOfHom b.2.unop) (leOfHom a.2.unop)
        ((scaledSchemes).map a).unop rfl ((scaledSchemes).map b).unop rfl
        ((scaledSchemes).map (a ≫ b)).unop rfl
        (congrArg Quiver.Hom.unop ((scaledSchemes).map_comp a b)).symm }

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
