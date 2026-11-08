import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCoarseRestriction
import Langlands.Shimura.Coefficients.VaryingSystemGroupCoverChange

/-! # Original coarse Harris coefficients along nested CM levels -/

noncomputable section

open CategoryTheory Opposite

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.Global Langlands.Shimura.Coefficients

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (U V T : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup) (hTV : T.obj.subgroup ≤ V.obj.subgroup)
  (m : ℕ) (hm : m ≠ 0)

local notation "hTU" => hTV.trans hVU
local notation "R" => HarrisCoefficientIntegers K p
local notation "levelT" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U T hTU m hm k
local notation "levelV" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "levelsT" => cmHarrisCoarseCoefficientLevels D ρ p U T hTU m hm
local notation "levelsV" => cmHarrisCoarseCoefficientLevels D ρ p U V hVU m hm
local notation "groupsT" => cmHarrisCoarseCoefficientGroups D ρ p U T hTU m hm
local notation "groupsV" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "coefficientsT" => cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm
local notation "coefficientsV" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm

omit [IsCMField F] [IsScalarTower E F A] in
/-- The actual intersections T ∩ U_k refine the original intersections V ∩ U_k. -/
theorem cmHarrisCoarseTowerLevel_le (k : ℕ) :
    (levelT k).obj.subgroup ≤ (levelV k).obj.subgroup := by
  rw [cmHarrisCoarseCoefficientLevel_subgroup, cmHarrisCoarseCoefficientLevel_subgroup]
  exact inf_le_inf_right _ hTV

/-- These actual inclusions preserve every exponent transition. -/
def cmHarrisCoarseTowerLevelComparison : levelsT ⟶ levelsV where
  app k := smallCMInclusion D
    (cmHarrisCoarseTowerLevel_le D ρ p U V T hVU hTV m hm k.unop)
  naturality i j f := by
    change smallCMInclusion D _ ≫ smallCMInclusion D _ =
      smallCMInclusion D _ ≫ smallCMInclusion D _
    rw [smallCMInclusion_trans, smallCMInclusion_trans]

omit [IsCMField F] [IsScalarTower E F A] in
/-- Both original routes from T ∩ U_k to V agree. -/
@[reassoc] theorem cmHarrisCoarseTowerLevelComparison_projection (k : ℕᵒᵖ) :
    (cmHarrisCoarseTowerLevelComparison D ρ p U V T hVU hTV m hm).app k ≫
        (cmHarrisCoarseCoefficientLevelProjection D ρ p U V hVU m hm).app k =
      (cmHarrisCoarseCoefficientLevelProjection D ρ p U T hTU m hm).app k ≫
        smallCMInclusion D hTV := by
  change smallCMInclusion D _ ≫ smallCMInclusion D _ =
    smallCMInclusion D _ ≫ smallCMInclusion D _
  rw [smallCMInclusion_trans, smallCMInclusion_trans]

omit [IsCMField F] [IsScalarTower E F A] in
/-- Both routes to the unchanged original U-kernel level agree. -/
@[reassoc] theorem cmHarrisCoarseTowerLevelComparison_original (k : ℕᵒᵖ) :
    (cmHarrisCoarseTowerLevelComparison D ρ p U V T hVU hTV m hm).app k ≫
        (cmHarrisCoarseCoefficientLevelComparison D ρ p U V hVU m hm).app k =
      (cmHarrisCoarseCoefficientLevelComparison D ρ p U T hTU m hm).app k := by
  change smallCMInclusion D _ ≫ smallCMInclusion D _ = smallCMInclusion D _
  rw [smallCMInclusion_trans]

/-- The actual inclusion T ≤ V induces a natural residual embedding at every exponent. -/
def cmHarrisCoarseTowerGroupMap : groupsT ⟶ groupsV where
  app k := GrpCat.ofHom (QuotientGroup.quotientMapSubgroupOfOfLe
    (cmHarrisCoarseTowerLevel_le D ρ p U V T hVU hTV m hm k.unop) hTV)
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "groupMap" => cmHarrisCoarseTowerGroupMap D ρ p U V T hVU hTV m hm
local notation "restriction" => EquivariantDiagram.groupRestriction (ModuleCat.{0} R) groupMap

/-- The residual map keeps the original T representative, included into V. -/
@[simp] theorem cmHarrisCoarseTowerGroupMap_mk (k : ℕᵒᵖ) (g : T.obj.subgroup) :
    ((groupMap).app k).hom (QuotientGroup.mk g) =
      QuotientGroup.mk (Subgroup.inclusion hTV g) := rfl

/-- The residual map is injective because the kernels are literal intersections with U_k. -/
theorem cmHarrisCoarseTowerGroupMap_injective (k : ℕᵒᵖ) :
    Function.Injective ((groupMap).app k).hom := by
  apply (injective_iff_map_eq_one _).mpr
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
    intro hg
    apply (QuotientGroup.eq_one_iff _).mpr
    change (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
      (levelT k.unop).obj.subgroup
    rw [cmHarrisCoarseCoefficientLevel_subgroup]
    refine ⟨g.property, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hTV g) :
      SmallCMResidualGroup D V (levelV k.unop)) = 1 at hg
    have hv := (QuotientGroup.eq_one_iff (Subgroup.inclusion hTV g)).mp hg
    change (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
      (levelV k.unop).obj.subgroup at hv
    rw [cmHarrisCoarseCoefficientLevel_subgroup] at hv
    exact hv.2

/-- Including into the original U-residual group commutes with the coarse tower map. -/
@[reassoc] theorem cmHarrisCoarseTowerGroupMap_original :
    groupMap ≫ cmHarrisCoarseCoefficientGroupMap D ρ p U V hVU m hm =
      cmHarrisCoarseCoefficientGroupMap D ρ p U T hTU m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- The original U-coefficient action is unchanged by the two residual restriction routes. -/
theorem cmHarrisCoarseTowerCoefficient_action (k : ℕᵒᵖ) (g : (groupsT).obj k) :
    ((restriction).obj coefficientsV).ρ k g = (coefficientsT).ρ k g := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- Identity on the complete original U-coefficient diagram identifies the two restrictions. -/
def cmHarrisCoarseTowerCoefficientIso :
    (restriction).obj coefficientsV ≅ coefficientsT where
  hom :=
    { hom := 𝟙 _
      comm k g := by
        change ((restriction).obj coefficientsV).ρ k g ≫ 𝟙 _ =
          𝟙 _ ≫ (coefficientsT).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact cmHarrisCoarseTowerCoefficient_action D ρ p U V T hVU hTV m hm k g }
  inv :=
    { hom := 𝟙 _
      comm k g := by
        change (coefficientsT).ρ k g ≫ 𝟙 _ =
          𝟙 _ ≫ ((restriction).obj coefficientsV).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact (cmHarrisCoarseTowerCoefficient_action D ρ p U V T hVU hTV m hm k g).symm }
  hom_inv_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _

@[simp] theorem cmHarrisCoarseTowerCoefficientIso_hom :
    (cmHarrisCoarseTowerCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisCoarseTowerCoefficientIso_inv :
    (cmHarrisCoarseTowerCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
