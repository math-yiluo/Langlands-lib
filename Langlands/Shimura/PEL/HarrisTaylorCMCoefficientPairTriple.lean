import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientTripleCommon
import Langlands.Shimura.Coefficients.GroupRestrictionComparison

/-! # Original pairwise coefficient systems restricted to the actual triple kernels -/

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
local notation "own" => cmHarrisTripleOwnCoefficients D ρ p U V T hVU hTV m hm
local notation "middle" => cmHarrisTripleMiddleCoefficients D ρ p U V T hVU hTV m hm
local notation "upper" => cmHarrisTripleUpperCoefficients D ρ p U V T hVU hTV m hm

local notation "directGroups" => cmHarrisLatticeCommonGroups D ρ p U T hTU m hm
local notation "directOwn" => cmHarrisLatticeCommonOwnCoefficients D ρ p U T hTU m hm
local notation "directOriginal" => cmHarrisLatticeCommonOriginalCoefficients D ρ p U T hTU m hm

local notation "tripleLevel" k:arg => cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm k
local notation "directLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p U T hTU m hm k
local notation "lowerLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p V T hTV m hm k
local notation "ownLevel" k:arg => cmHarrisCoefficientLevel D ρ p T m hm k
local notation "upperLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U T hTU m hm k
local notation "middleLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p V T hTV m hm k

/-- The actual triple quotient maps naturally to the original direct pair quotient. -/
def cmHarrisTripleDirectPairGroupMap : groups ⟶ directGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D T (directLevel j.unop)
      (tripleLevel j.unop) (tripleLevel i.unop)
      (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm j.unop)
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))).trans
      (smallCMResidualQuotientMap_comp D T (directLevel j.unop)
        (directLevel i.unop) (tripleLevel i.unop)
        (cmHarrisLatticeCommonLevel_antitone D ρ p U T hTU m hm (leOfHom f.unop))
        (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm i.unop)).symm

local notation "directMap" => cmHarrisTripleDirectPairGroupMap D ρ p U V T hVU hTV m hm
local notation "directRestriction" => EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directMap

/-- The component homomorphisms compose to the original own quotient map. -/
theorem cmHarrisTripleDirectPairGroupMap_own_app (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonOwnGroupMap D ρ p U T hTU m hm).app k).hom.comp
        ((directMap).app k).hom =
      ((cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm).app k).hom :=
  smallCMResidualQuotientMap_comp D T (ownLevel k.unop) (directLevel k.unop)
    (tripleLevel k.unop)
    (cmHarrisLatticeCommonLevel_le_own D ρ p U T hTU m hm k.unop)
    (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k.unop)

/-- The same composition identity holds for the complete quotient diagrams. -/
@[reassoc] theorem cmHarrisTripleDirectPairGroupMap_own :
    directMap ≫ cmHarrisLatticeCommonOwnGroupMap D ρ p U T hTU m hm =
      cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleDirectPairGroupMap_own_app D ρ p U V T hVU hTV m hm k

/-- The component homomorphisms compose to the original upper quotient map. -/
theorem cmHarrisTripleDirectPairGroupMap_original_app (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonCoarseGroupMap D ρ p U T hTU m hm).app k).hom.comp
        ((directMap).app k).hom =
      ((cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm).app k).hom :=
  smallCMResidualQuotientMap_comp D T (upperLevel k.unop) (directLevel k.unop)
    (tripleLevel k.unop)
    (cmHarrisLatticeCommonLevel_le_coarse D ρ p U T hTU m hm k.unop)
    (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k.unop)

/-- The same composition identity holds for the complete quotient diagrams. -/
@[reassoc] theorem cmHarrisTripleDirectPairGroupMap_original :
    directMap ≫ cmHarrisLatticeCommonCoarseGroupMap D ρ p U T hTU m hm =
      cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleDirectPairGroupMap_original_app D ρ p U V T hVU hTV m hm k

/-- Identity on the complete original coefficient functor identifies the two action factorizations. -/
def cmHarrisTripleDirectPairOwnCoefficientIso :
    (directRestriction).obj directOwn ≅ own :=
  EquivariantDiagram.groupRestrictionCompIso directMap
    (cmHarrisLatticeCommonOwnGroupMap D ρ p U T hTU m hm)
    (cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm)
    (cmHarrisTripleDirectPairGroupMap_own_app D ρ p U V T hVU hTV m hm)
    (cmHarrisCoefficientDiagram D ρ p T m hm)

/-- No coefficient or exponent transition is changed by this identification. -/
@[simp] theorem cmHarrisTripleDirectPairOwnCoefficientIso_hom :
    (cmHarrisTripleDirectPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleDirectPairOwnCoefficientIso_inv :
    (cmHarrisTripleDirectPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Identity on the complete original coefficient functor identifies the two action factorizations. -/
def cmHarrisTripleDirectPairOriginalCoefficientIso :
    (directRestriction).obj directOriginal ≅ upper :=
  EquivariantDiagram.groupRestrictionCompIso directMap
    (cmHarrisLatticeCommonCoarseGroupMap D ρ p U T hTU m hm)
    (cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm)
    (cmHarrisTripleDirectPairGroupMap_original_app D ρ p U V T hVU hTV m hm)
    (cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm)

/-- No coefficient or exponent transition is changed by this identification. -/
@[simp] theorem cmHarrisTripleDirectPairOriginalCoefficientIso_hom :
    (cmHarrisTripleDirectPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleDirectPairOriginalCoefficientIso_inv :
    (cmHarrisTripleDirectPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Restriction of the original pair inclusion is the original triple inclusion, through identity coefficients. -/
@[reassoc] theorem cmHarrisTripleDirectPairCoefficientInclusion_square :
    (directRestriction).map (cmHarrisLatticeCommonCoefficientInclusion D ρ p U T hTU m hm) ≫
        (cmHarrisTripleDirectPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom =
      (cmHarrisTripleDirectPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom ≫
        cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm := by
  apply EquivariantDiagram.Hom.ext
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

local notation "lowerGroups" => cmHarrisLatticeCommonGroups D ρ p V T hTV m hm
local notation "lowerOwn" => cmHarrisLatticeCommonOwnCoefficients D ρ p V T hTV m hm
local notation "lowerOriginal" => cmHarrisLatticeCommonOriginalCoefficients D ρ p V T hTV m hm

/-- The actual triple quotient maps naturally to the original lower pair quotient. -/
def cmHarrisTripleLowerPairGroupMap : groups ⟶ lowerGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D T (lowerLevel j.unop)
      (tripleLevel j.unop) (tripleLevel i.unop)
      (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm j.unop)
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))).trans
      (smallCMResidualQuotientMap_comp D T (lowerLevel j.unop)
        (lowerLevel i.unop) (tripleLevel i.unop)
        (cmHarrisLatticeCommonLevel_antitone D ρ p V T hTV m hm (leOfHom f.unop))
        (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm i.unop)).symm

local notation "lowerMap" => cmHarrisTripleLowerPairGroupMap D ρ p U V T hVU hTV m hm
local notation "lowerRestriction" => EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerMap

/-- The component homomorphisms compose to the original own quotient map. -/
theorem cmHarrisTripleLowerPairGroupMap_own_app (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonOwnGroupMap D ρ p V T hTV m hm).app k).hom.comp
        ((lowerMap).app k).hom =
      ((cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm).app k).hom :=
  smallCMResidualQuotientMap_comp D T (ownLevel k.unop) (lowerLevel k.unop)
    (tripleLevel k.unop)
    (cmHarrisLatticeCommonLevel_le_own D ρ p V T hTV m hm k.unop)
    (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k.unop)

/-- The same composition identity holds for the complete quotient diagrams. -/
@[reassoc] theorem cmHarrisTripleLowerPairGroupMap_own :
    lowerMap ≫ cmHarrisLatticeCommonOwnGroupMap D ρ p V T hTV m hm =
      cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleLowerPairGroupMap_own_app D ρ p U V T hVU hTV m hm k

/-- The component homomorphisms compose to the original middle quotient map. -/
theorem cmHarrisTripleLowerPairGroupMap_original_app (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonCoarseGroupMap D ρ p V T hTV m hm).app k).hom.comp
        ((lowerMap).app k).hom =
      ((cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm).app k).hom :=
  smallCMResidualQuotientMap_comp D T (middleLevel k.unop) (lowerLevel k.unop)
    (tripleLevel k.unop)
    (cmHarrisLatticeCommonLevel_le_coarse D ρ p V T hTV m hm k.unop)
    (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k.unop)

/-- The same composition identity holds for the complete quotient diagrams. -/
@[reassoc] theorem cmHarrisTripleLowerPairGroupMap_original :
    lowerMap ≫ cmHarrisLatticeCommonCoarseGroupMap D ρ p V T hTV m hm =
      cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm := by
  apply NatTrans.ext
  funext k
  apply GrpCat.hom_ext
  exact cmHarrisTripleLowerPairGroupMap_original_app D ρ p U V T hVU hTV m hm k

/-- Identity on the complete original coefficient functor identifies the two action factorizations. -/
def cmHarrisTripleLowerPairOwnCoefficientIso :
    (lowerRestriction).obj lowerOwn ≅ own :=
  EquivariantDiagram.groupRestrictionCompIso lowerMap
    (cmHarrisLatticeCommonOwnGroupMap D ρ p V T hTV m hm)
    (cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm)
    (cmHarrisTripleLowerPairGroupMap_own_app D ρ p U V T hVU hTV m hm)
    (cmHarrisCoefficientDiagram D ρ p T m hm)

/-- No coefficient or exponent transition is changed by this identification. -/
@[simp] theorem cmHarrisTripleLowerPairOwnCoefficientIso_hom :
    (cmHarrisTripleLowerPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleLowerPairOwnCoefficientIso_inv :
    (cmHarrisTripleLowerPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Identity on the complete original coefficient functor identifies the two action factorizations. -/
def cmHarrisTripleLowerPairOriginalCoefficientIso :
    (lowerRestriction).obj lowerOriginal ≅ middle :=
  EquivariantDiagram.groupRestrictionCompIso lowerMap
    (cmHarrisLatticeCommonCoarseGroupMap D ρ p V T hTV m hm)
    (cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm)
    (cmHarrisTripleLowerPairGroupMap_original_app D ρ p U V T hVU hTV m hm)
    (cmHarrisCoarseCoefficientDiagram D ρ p V T hTV m hm)

/-- No coefficient or exponent transition is changed by this identification. -/
@[simp] theorem cmHarrisTripleLowerPairOriginalCoefficientIso_hom :
    (cmHarrisTripleLowerPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom.hom = 𝟙 _ := rfl

@[simp] theorem cmHarrisTripleLowerPairOriginalCoefficientIso_inv :
    (cmHarrisTripleLowerPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).inv.hom = 𝟙 _ := rfl

/-- Restriction of the original pair inclusion is the original triple inclusion, through identity coefficients. -/
@[reassoc] theorem cmHarrisTripleLowerPairCoefficientInclusion_square :
    (lowerRestriction).map (cmHarrisLatticeCommonCoefficientInclusion D ρ p V T hTV m hm) ≫
        (cmHarrisTripleLowerPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm).hom =
      (cmHarrisTripleLowerPairOwnCoefficientIso D ρ p U V T hVU hTV m hm).hom ≫
        cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm := by
  apply EquivariantDiagram.Hom.ext
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
