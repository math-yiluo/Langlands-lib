import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLevelSystem
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # Three original canonical coefficient systems on their actual common CM kernels -/

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
local notation "basePair" k:arg => cmHarrisLatticeCommonLevel D ρ p U T hTU m hm k
local notation "middleLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p V T hTV m hm k
local notation "ownLevel" k:arg => cmHarrisCoefficientLevel D ρ p T m hm k
local notation "upperLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U T hTU m hm k
local notation "ownGroups" => cmHarrisCoefficientGroups D ρ p T m hm
local notation "middleGroups" => cmHarrisCoarseCoefficientGroups D ρ p V T hTV m hm
local notation "upperGroups" => cmHarrisCoarseCoefficientGroups D ρ p U T hTU m hm
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p T m hm
local notation "middleCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p V T hTV m hm
local notation "upperCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm
local notation "ownSystem" => cmHarrisTorsionSystem D ρ p T m
local notation "middleSystem" => cmHarrisCoarseTorsionSystem D ρ p V T hTV m
local notation "upperSystem" => cmHarrisCoarseTorsionSystem D ρ p U T hTU m

/-- The literal small intersection killing all three original coefficient actions inside T. -/
def cmHarrisTripleCommonLevel (k : ℕ) : SmallCMLevel D :=
  smallCMCommonLevel D (basePair k) (middleLevel k)

local notation "commonLevel" k:arg => cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm k

omit [IsCMField F] [IsScalarTower E F A] in
/-- Its subgroup is exactly the indicated intersection of the existing actual levels. -/
@[simp] theorem cmHarrisTripleCommonLevel_subgroup (k : ℕ) :
    (commonLevel k).obj.subgroup =
      (basePair k).obj.subgroup ⊓ (middleLevel k).obj.subgroup :=
  smallCMCommonLevel_subgroup D _ _

omit [IsCMField F] [IsScalarTower E F A] in
/-- The common level refines the original direct T-to-U comparison cover. -/
theorem cmHarrisTripleCommonLevel_le_pair (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (basePair k).obj.subgroup :=
  smallCMCommonLevel_le_left D _ _

omit [IsCMField F] [IsScalarTower E F A] in
/-- The common level also refines the original restricted V coefficient kernel. -/
theorem cmHarrisTripleCommonLevel_le_middle (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (middleLevel k).obj.subgroup :=
  smallCMCommonLevel_le_right D _ _

omit [IsCMField F] [IsScalarTower E F A] in
/-- It refines the original T coefficient kernel. -/
theorem cmHarrisTripleCommonLevel_le_own (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (ownLevel k).obj.subgroup :=
  (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k).trans
    (cmHarrisLatticeCommonLevel_le_own D ρ p U T hTU m hm k)

omit [IsCMField F] [IsScalarTower E F A] in
/-- It refines the original restricted U coefficient kernel. -/
theorem cmHarrisTripleCommonLevel_le_upper (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (upperLevel k).obj.subgroup :=
  (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k).trans
    (cmHarrisLatticeCommonLevel_le_coarse D ρ p U T hTU m hm k)

/-- Every common cover is over the same actual coarse T level. -/
theorem cmHarrisTripleCommonLevel_le (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ T.obj.subgroup :=
  (cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k).trans
    (cmHarrisCoefficientLevel_le D ρ p T m hm k)

/-- The subgroup inside T is precisely the common kernel of all three original actions. -/
theorem cmHarrisTripleCommonLevel_subgroupOf (k : ℕ) :
    (commonLevel k).obj.subgroup.subgroupOf T.obj.subgroup =
      (((ownSystem).obj (op k)).ρ.ker ⊓ ((upperSystem).obj (op k)).ρ.ker) ⊓
        ((middleSystem).obj (op k)).ρ.ker := by
  rw [cmHarrisTripleCommonLevel_subgroup]
  change (basePair k).obj.subgroup.subgroupOf T.obj.subgroup ⊓
    (middleLevel k).obj.subgroup.subgroupOf T.obj.subgroup = _
  rw [cmHarrisLatticeCommonLevel_subgroupOf, cmHarrisCoarseCoefficientLevel_eq_ker]

instance cmHarrisTripleCommonLevel_normal (k : ℕ) :
    ((commonLevel k).obj.subgroup.subgroupOf T.obj.subgroup).Normal := by
  rw [cmHarrisTripleCommonLevel_subgroupOf]
  infer_instance

omit [IsCMField F] [IsScalarTower E F A] in
/-- The actual common kernel levels refine antitonically in the original exponent order. -/
theorem cmHarrisTripleCommonLevel_antitone :
    Antitone (fun k => (commonLevel k).obj.subgroup) := by
  intro i j hij
  change (commonLevel j).obj.subgroup ≤ (commonLevel i).obj.subgroup
  rw [cmHarrisTripleCommonLevel_subgroup, cmHarrisTripleCommonLevel_subgroup]
  exact inf_le_inf (cmHarrisLatticeCommonLevel_antitone D ρ p U T hTU m hm hij)
    (cmHarrisCoarseCoefficientLevel_antitone D ρ p V T hTV m hm hij)

omit [IsCMField F] [IsScalarTower E F A] in
/-- It also refines the actual T-to-V pair comparison cover. -/
theorem cmHarrisTripleCommonLevel_le_lowerPair (k : ℕ) :
    (commonLevel k).obj.subgroup ≤
      (cmHarrisLatticeCommonLevel D ρ p V T hTV m hm k).obj.subgroup := by
  rw [cmHarrisLatticeCommonLevel_subgroup]
  exact le_inf (cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k)
    (cmHarrisTripleCommonLevel_le_middle D ρ p U V T hVU hTV m hm k)

/-- Its original tower map also reaches the actual V-to-U pair comparison cover. -/
theorem cmHarrisTripleCommonLevel_le_upperPair (k : ℕ) :
    (commonLevel k).obj.subgroup ≤
      (cmHarrisLatticeCommonLevel D ρ p U V hVU m hm k).obj.subgroup := by
  rw [cmHarrisLatticeCommonLevel_subgroup]
  apply le_inf
  · exact (cmHarrisTripleCommonLevel_le_middle D ρ p U V T hVU hTV m hm k).trans
      (cmHarrisCoarseCoefficientLevel_le_original D ρ p V T hTV m hm k)
  · rw [cmHarrisCoarseCoefficientLevel_subgroup]
    exact le_inf ((cmHarrisTripleCommonLevel_le D ρ p U V T hVU hTV m hm k).trans hTV)
      ((cmHarrisTripleCommonLevel_le_upper D ρ p U V T hVU hTV m hm k).trans
        (cmHarrisCoarseCoefficientLevel_le_original D ρ p U T hTU m hm k))

/-- All actual common levels and their identity-transporter inclusions form an inverse diagram. -/
def cmHarrisTripleCommonLevels : ℕᵒᵖ ⥤ SmallCMLevel D where
  obj k := commonLevel k.unop
  map f := smallCMInclusion D
    (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))
  map_id _ := smallCMInclusion_refl D _
  map_comp _ _ := (smallCMInclusion_trans D _ _).symm

/-- The actual finite residual quotients of the common kernels inside T. -/
def cmHarrisTripleCommonGroups : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of (SmallCMResidualGroup D T (commonLevel k.unop))
  map f := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop)))
  map_id _ := by
    apply GrpCat.hom_ext
    exact smallCMResidualQuotientMap_refl D T _
  map_comp f g := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D T _ _ _
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom g.unop))
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))).symm

local notation "groups" => cmHarrisTripleCommonGroups D ρ p U V T hVU hTV m hm

theorem cmHarrisTripleCommonGroups_finite (k : ℕᵒᵖ) : Finite ((groups).obj k) :=
  smallCMResidualGroup_finite D T _

/-- The actual common residual groups map naturally to the original own quotient diagram. -/
def cmHarrisTripleOwnGroupMap : groups ⟶ ownGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "ownGroupMap" => cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm

/-- The full original own coefficient functor with its action through the actual common quotient. -/
def cmHarrisTripleOwnCoefficients : EquivariantDiagram groups (ModuleCat R) where
  obj := (ownCoefficients).obj
  ρ k := ((ownCoefficients).ρ k).comp ((ownGroupMap).app k).hom
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((ownSystem).map f).comm g

local notation "ownCommon" => cmHarrisTripleOwnCoefficients D ρ p U V T hVU hTV m hm

/-- The actual common residual groups map naturally to the original middle quotient diagram. -/
def cmHarrisTripleMiddleGroupMap : groups ⟶ middleGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_le_middle D ρ p U V T hVU hTV m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "middleGroupMap" => cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm

/-- The full original middle coefficient functor with its action through the actual common quotient. -/
def cmHarrisTripleMiddleCoefficients : EquivariantDiagram groups (ModuleCat R) where
  obj := (middleCoefficients).obj
  ρ k := ((middleCoefficients).ρ k).comp ((middleGroupMap).app k).hom
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((middleSystem).map f).comm g

local notation "middleCommon" => cmHarrisTripleMiddleCoefficients D ρ p U V T hVU hTV m hm

/-- The actual common residual groups map naturally to the original upper quotient diagram. -/
def cmHarrisTripleUpperGroupMap : groups ⟶ upperGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D T _ _
    (cmHarrisTripleCommonLevel_le_upper D ρ p U V T hVU hTV m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "upperGroupMap" => cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm

/-- The full original upper coefficient functor with its action through the actual common quotient. -/
def cmHarrisTripleUpperCoefficients : EquivariantDiagram groups (ModuleCat R) where
  obj := (upperCoefficients).obj
  ρ k := ((upperCoefficients).ρ k).comp ((upperGroupMap).app k).hom
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((upperSystem).map f).comm g

local notation "upperCommon" => cmHarrisTripleUpperCoefficients D ρ p U V T hVU hTV m hm

/-- The actual T-to-V lattice inclusion, with the original T action. -/
def cmHarrisTripleLowerCoefficientInclusion : ownCommon ⟶ middleCommon where
  hom := Functor.whiskerRight (cmHarrisTorsionSystemInclusion D ρ p V T hTV m)
    (Action.forget (ModuleCat R) T.obj.subgroup)
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisTorsionSystemInclusion D ρ p V T hTV m).app k).comm g

/-- The actual V-to-U lattice inclusion, restricted along the original T-to-V subgroup inclusion. -/
def cmHarrisTripleUpperCoefficientInclusion : middleCommon ⟶ upperCommon where
  hom := Functor.whiskerRight
    (Functor.whiskerRight (cmHarrisTorsionSystemInclusion D ρ p U V hVU m)
      (Action.res (ModuleCat R) (Subgroup.inclusion hTV)))
    (Action.forget (ModuleCat R) T.obj.subgroup)
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      exact ((cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app k).comm (Subgroup.inclusion hTV g)

/-- The original direct T-to-U lattice inclusion on the same common quotient diagram. -/
def cmHarrisTripleDirectCoefficientInclusion : ownCommon ⟶ upperCommon where
  hom := Functor.whiskerRight (cmHarrisTorsionSystemInclusion D ρ p U T hTU m)
    (Action.forget (ModuleCat R) T.obj.subgroup)
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisTorsionSystemInclusion D ρ p U T hTU m).app k).comm g

local notation "lowerInclusion" => cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm
local notation "upperInclusion" => cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm
local notation "directInclusion" => cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm

/-- The two actual coefficient maps compose to the original direct included-vector map. -/
@[reassoc] theorem cmHarrisTripleCoefficientInclusion_comp :
    lowerInclusion ≫ upperInclusion = directInclusion := by
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext k
  exact cmHarrisTorsionSystemInclusion_comp D ρ p m k U V T hVU hTV

/-- The complete coefficient chain lives on one actual finite common-kernel diagram. -/
def cmHarrisTripleCoefficientChain :
    ComposableArrows (EquivariantDiagram groups (ModuleCat R)) 2 :=
  ComposableArrows.mk₂ lowerInclusion upperInclusion

local notation "chain" => cmHarrisTripleCoefficientChain D ρ p U V T hVU hTV m hm

@[simp] theorem cmHarrisTripleCoefficientChain_lower :
    (chain).map' 0 1 = lowerInclusion := rfl

@[simp] theorem cmHarrisTripleCoefficientChain_upper :
    (chain).map' 1 2 = upperInclusion := rfl

/-- The full chain's composite is exactly the original direct coefficient inclusion. -/
@[simp] theorem cmHarrisTripleCoefficientChain_hom : (chain).hom = directInclusion :=
  cmHarrisTripleCoefficientInclusion_comp D ρ p U V T hVU hTV m hm

/-- The direct map retains the original full-lattice representative formula. -/
@[simp] theorem cmHarrisTripleDirectCoefficientInclusion_mk (k : ℕᵒᵖ)
    (x : harrisLattice ρ p (CompactOpenLevel.inverseOpposite T.obj)) :
    ((directInclusion).hom.app k).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (harrisLatticeInclusion ρ p
        (CompactOpenLevel.inverseOpposite U.obj) (CompactOpenLevel.inverseOpposite T.obj)
        (CompactOpenLevel.inverseOpposite_mono hTU) x) := rfl

/-- Every original exponent reduction commutes with the direct comparison. -/
@[reassoc] theorem cmHarrisTripleDirectCoefficientInclusion_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownCommon).obj.map f ≫ (directInclusion).hom.app j =
      (directInclusion).hom.app i ≫ (upperCommon).obj.map f :=
  (directInclusion).hom.naturality f

/-- The T-to-V leg retains all original exponent reductions. -/
@[reassoc] theorem cmHarrisTripleLowerCoefficientInclusion_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownCommon).obj.map f ≫ (lowerInclusion).hom.app j =
      (lowerInclusion).hom.app i ≫ (middleCommon).obj.map f :=
  (lowerInclusion).hom.naturality f

/-- The restricted V-to-U leg also retains all original exponent reductions. -/
@[reassoc] theorem cmHarrisTripleUpperCoefficientInclusion_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (middleCommon).obj.map f ≫ (upperInclusion).hom.app j =
      (upperInclusion).hom.app i ≫ (upperCommon).obj.map f :=
  (upperInclusion).hom.naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
