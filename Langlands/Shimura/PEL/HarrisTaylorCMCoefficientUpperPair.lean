import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientTripleCommon
import Langlands.Shimura.Coefficients.VaryingSystemGroupCoverChange

/-! # The original upper pair coefficients restricted to actual triple CM kernels -/

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
local notation "groups" => cmHarrisTripleCommonGroups D ρ p U V T hVU hTV m hm
local notation "pairGroups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "pairOwn" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "pairOriginal" => cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm
local notation "middle" => cmHarrisTripleMiddleCoefficients D ρ p U V T hVU hTV m hm
local notation "upper" => cmHarrisTripleUpperCoefficients D ρ p U V T hVU hTV m hm

/-- The actual inclusion T ≤ V induces a natural map from triple residuals to upper-pair residuals. -/
def cmHarrisTripleUpperPairGroupMap : groups ⟶ pairGroups where
  app k := GrpCat.ofHom (QuotientGroup.quotientMapSubgroupOfOfLe
    (cmHarrisTripleCommonLevel_le_upperPair D ρ p U V T hVU hTV m hm k.unop) hTV)
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "pairMap" => cmHarrisTripleUpperPairGroupMap D ρ p U V T hVU hTV m hm
local notation "restriction" => EquivariantDiagram.groupRestriction (ModuleCat.{0} R) pairMap

/-- This map retains the original representative, included from T into V. -/
@[simp] theorem cmHarrisTripleUpperPairGroupMap_mk (k : ℕᵒᵖ) (g : T.obj.subgroup) :
    ((pairMap).app k).hom (QuotientGroup.mk g) =
      QuotientGroup.mk (Subgroup.inclusion hTV g) := rfl

/-- The original pair own quotient route equals the original triple middle route to V/V_k. -/
theorem cmHarrisTripleUpperPairGroupMap_own_app (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonOwnGroupMap D ρ p U V hVU m hm).app k).hom.comp
        ((pairMap).app k).hom =
      ((cmHarrisCoarseCoefficientGroupMap D ρ p V T hTV m hm).app k).hom.comp
        ((cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm).app k).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- The same identity holds for the entire original residual diagrams. -/
@[reassoc] theorem cmHarrisTripleUpperPairGroupMap_own :
    pairMap ≫ cmHarrisLatticeCommonOwnGroupMap D ρ p U V hVU m hm =
      cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm ≫
        cmHarrisCoarseCoefficientGroupMap D ρ p V T hTV m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleUpperPairGroupMap_own_app D ρ p U V T hVU hTV m hm k

/-- Both original upper quotient routes reach the same element of U/U_k. -/
theorem cmHarrisTripleUpperPairGroupMap_original_app (k : ℕᵒᵖ) :
    (((cmHarrisCoarseCoefficientGroupMap D ρ p U V hVU m hm).app k).hom.comp
        ((cmHarrisLatticeCommonCoarseGroupMap D ρ p U V hVU m hm).app k).hom).comp
          ((pairMap).app k).hom =
      ((cmHarrisCoarseCoefficientGroupMap D ρ p U T hTU m hm).app k).hom.comp
        ((cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm).app k).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- This upper identity also retains the complete original exponent diagrams. -/
@[reassoc] theorem cmHarrisTripleUpperPairGroupMap_original :
    (pairMap ≫ cmHarrisLatticeCommonCoarseGroupMap D ρ p U V hVU m hm) ≫
        cmHarrisCoarseCoefficientGroupMap D ρ p U V hVU m hm =
      cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm ≫
        cmHarrisCoarseCoefficientGroupMap D ρ p U T hTU m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleUpperPairGroupMap_original_app D ρ p U V T hVU hTV m hm k

/-- The original V-coefficient actions agree after the actual quotient restrictions. -/
theorem cmHarrisTripleUpperPairOwnCoefficient_action (k : ℕᵒᵖ) (g : (groups).obj k) :
    ((restriction).obj pairOwn).ρ k g = (middle).ρ k g := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- The original U-coefficient actions agree after the actual quotient restrictions. -/
theorem cmHarrisTripleUpperPairOriginalCoefficient_action (k : ℕᵒᵖ) (g : (groups).obj k) :
    ((restriction).obj pairOriginal).ρ k g = (upper).ρ k g := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- Identity on the full original V-coefficient diagram identifies upper-pair own with triple middle. -/
def cmHarrisTripleUpperPairOwnCoefficientIso :
    (restriction).obj pairOwn ≅ middle where
  hom :=
    { hom := 𝟙 _
      comm k g := by
        change ((restriction).obj pairOwn).ρ k g ≫ 𝟙 _ = 𝟙 _ ≫ (middle).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact cmHarrisTripleUpperPairOwnCoefficient_action D ρ p U V T hVU hTV m hm k g }
  inv :=
    { hom := 𝟙 _
      comm k g := by
        change (middle).ρ k g ≫ 𝟙 _ = 𝟙 _ ≫ ((restriction).obj pairOwn).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact (cmHarrisTripleUpperPairOwnCoefficient_action D ρ p U V T hVU hTV m hm k g).symm }
  hom_inv_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _

/-- Both underlying maps are identity on the whole unchanged exponent diagram. -/
@[simp] theorem cmHarrisTripleUpperPairOwnCoefficientIso_hom :
    (cmHarrisTripleUpperPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleUpperPairOwnCoefficientIso_inv :
    (cmHarrisTripleUpperPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Identity on the full original U-coefficient diagram identifies upper-pair original with triple upper. -/
def cmHarrisTripleUpperPairOriginalCoefficientIso :
    (restriction).obj pairOriginal ≅ upper where
  hom :=
    { hom := 𝟙 _
      comm k g := by
        change ((restriction).obj pairOriginal).ρ k g ≫ 𝟙 _ = 𝟙 _ ≫ (upper).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact cmHarrisTripleUpperPairOriginalCoefficient_action D ρ p U V T hVU hTV m hm k g }
  inv :=
    { hom := 𝟙 _
      comm k g := by
        change (upper).ρ k g ≫ 𝟙 _ = 𝟙 _ ≫ ((restriction).obj pairOriginal).ρ k g
        simp only [Category.comp_id, Category.id_comp]
        exact (cmHarrisTripleUpperPairOriginalCoefficient_action D ρ p U V T hVU hTV m hm k g).symm }
  hom_inv_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply EquivariantDiagram.Hom.ext; exact Category.id_comp _

@[simp] theorem cmHarrisTripleUpperPairOriginalCoefficientIso_hom :
    (cmHarrisTripleUpperPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleUpperPairOriginalCoefficientIso_inv :
    (cmHarrisTripleUpperPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Restriction of the original upper-pair lattice inclusion is exactly the original triple upper inclusion. -/
@[reassoc] theorem cmHarrisTripleUpperPairCoefficientInclusion_square :
    (restriction).map (cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm) ≫
        (cmHarrisTripleUpperPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom =
      (cmHarrisTripleUpperPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom ≫
        cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm := by
  apply EquivariantDiagram.Hom.ext
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
