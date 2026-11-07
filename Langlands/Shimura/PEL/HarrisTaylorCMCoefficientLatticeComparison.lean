import Langlands.Shimura.Coefficients.HarrisLatticeLevelInclusion
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCoarseRestriction

/-! # Actual CM lattice comparison on common coefficient kernels -/

noncomputable section

open CategoryTheory Opposite

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura

namespace CompactOpenLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inverse-unop transport preserves an actual inclusion of compact open levels. -/
theorem inverseOpposite_mono {U V : CompactOpenLevel Gᵐᵒᵖ}
    (hVU : V.subgroup ≤ U.subgroup) :
    (inverseOpposite V).subgroup ≤ (inverseOpposite U).subgroup :=
  fun _ hx => hVU hx

end CompactOpenLevel

namespace PEL.HarrisTaylorCMWeilLevel

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
  (p : Global.FinitePlace ℚ) (U V : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup)

local notation "R" => HarrisCoefficientIntegers K p
local notation "ordinaryU" => CompactOpenLevel.inverseOpposite U.obj
local notation "ordinaryV" => CompactOpenLevel.inverseOpposite V.obj
local notation "ordinaryInclusion" => CompactOpenLevel.inverseOpposite_mono hVU
local notation "torsionInclusion" m:arg =>
  harrisTorsionSystemInclusion ρ p ordinaryU ordinaryV ordinaryInclusion m

/-- The actual inclusion of independently constructed lattices, with both actions
transported by the original inverse-unop convention. -/
def cmHarrisTorsionSystemInclusion (m : ℕ) :
    cmHarrisTorsionSystem D ρ p V m ⟶
      cmHarrisCoarseTorsionSystem D ρ p U V hVU m where
  app k :=
    { hom := ((torsionInclusion m).app k).hom
      comm g := ((torsionInclusion m).app k).comm
        (CompactOpenLevel.inverseOppositeEquiv V.obj g) }
  naturality {i j} f := by
    apply Action.Hom.ext
    have hnat := congrArg Action.Hom.hom ((torsionInclusion m).naturality f)
    exact hnat

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Its component retains the same vector of the original full tensor module. -/
@[simp] theorem cmHarrisTorsionSystemInclusion_mk (m : ℕ) (k : ℕᵒᵖ)
    (x : harrisLattice ρ p ordinaryV) :
    ((cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app k).hom.hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (harrisLatticeInclusion ρ p ordinaryU ordinaryV ordinaryInclusion x) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Every original exponent reduction commutes with the actual CM inclusion. -/
@[reassoc] theorem cmHarrisTorsionSystemInclusion_transition (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (cmHarrisTorsionSystem D ρ p V m).map f ≫
        (cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app j =
      (cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app i ≫
        (cmHarrisCoarseTorsionSystem D ρ p U V hVU m).map f :=
  (cmHarrisTorsionSystemInclusion D ρ p U V hVU m).naturality f

variable (m : ℕ) (hm : m ≠ 0)

local notation "ownLevel" k:arg => cmHarrisCoefficientLevel D ρ p V m hm k
local notation "coarseLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "ownGroups" => cmHarrisCoefficientGroups D ρ p V m hm
local notation "coarseGroups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p V m hm
local notation "coarseCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm

/-- An actual common small level for the two independently constructed coefficients. -/
def cmHarrisLatticeCommonLevel (k : ℕ) : SmallCMLevel D :=
  smallCMCommonLevel D (ownLevel k) (coarseLevel k)

local notation "commonLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p U V hVU m hm k

omit [IsCMField F] [IsScalarTower E F A] in
/-- The common level is the literal intersection of the two coefficient levels. -/
@[simp] theorem cmHarrisLatticeCommonLevel_subgroup (k : ℕ) :
    (commonLevel k).obj.subgroup =
      (ownLevel k).obj.subgroup ⊓ (coarseLevel k).obj.subgroup :=
  smallCMCommonLevel_subgroup D _ _

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmHarrisLatticeCommonLevel_le_own (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (ownLevel k).obj.subgroup :=
  smallCMCommonLevel_le_left D _ _

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmHarrisLatticeCommonLevel_le_coarse (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ (coarseLevel k).obj.subgroup :=
  smallCMCommonLevel_le_right D _ _

theorem cmHarrisLatticeCommonLevel_le (k : ℕ) :
    (commonLevel k).obj.subgroup ≤ V.obj.subgroup :=
  (cmHarrisLatticeCommonLevel_le_own D ρ p U V hVU m hm k).trans
    (cmHarrisCoefficientLevel_le D ρ p V m hm k)

/-- Both coefficient actions are killed by precisely the indicated common kernel. -/
theorem cmHarrisLatticeCommonLevel_subgroupOf (k : ℕ) :
    (commonLevel k).obj.subgroup.subgroupOf V.obj.subgroup =
      ((cmHarrisTorsionSystem D ρ p V m).obj (op k)).ρ.ker ⊓
        ((cmHarrisCoarseTorsionSystem D ρ p U V hVU m).obj (op k)).ρ.ker := by
  rw [cmHarrisLatticeCommonLevel_subgroup]
  change (ownLevel k).obj.subgroup.subgroupOf V.obj.subgroup ⊓
      (coarseLevel k).obj.subgroup.subgroupOf V.obj.subgroup = _
  rw [cmHarrisCoefficientLevel_subgroupOf, cmHarrisTorsionSystem_ker,
    cmHarrisCoarseCoefficientLevel_eq_ker]

instance cmHarrisLatticeCommonLevel_normal (k : ℕ) :
    ((commonLevel k).obj.subgroup.subgroupOf V.obj.subgroup).Normal := by
  rw [cmHarrisLatticeCommonLevel_subgroupOf]
  infer_instance

omit [IsCMField F] [IsScalarTower E F A] in
/-- The common levels refine with the original exponent order. -/
theorem cmHarrisLatticeCommonLevel_antitone :
    Antitone (fun k => (commonLevel k).obj.subgroup) := by
  intro i j hij
  change (commonLevel j).obj.subgroup ≤ (commonLevel i).obj.subgroup
  rw [cmHarrisLatticeCommonLevel_subgroup, cmHarrisLatticeCommonLevel_subgroup]
  exact inf_le_inf (cmHarrisCoefficientLevel_antitone D ρ p V m hm hij)
    (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm hij)

/-- The common kernels form an actual diagram of small CM levels. -/
def cmHarrisLatticeCommonLevels : ℕᵒᵖ ⥤ SmallCMLevel D where
  obj k := commonLevel k.unop
  map f := smallCMInclusion D
    (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))
  map_id _ := smallCMInclusion_refl D _
  map_comp _ _ := (smallCMInclusion_trans D _ _).symm

/-- The finite residual quotient diagram of the actual common kernels. -/
def cmHarrisLatticeCommonGroups : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of (SmallCMResidualGroup D V (commonLevel k.unop))
  map f := GrpCat.ofHom (smallCMResidualQuotientMap D V _ _
    (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop)))
  map_id _ := by
    apply GrpCat.hom_ext
    exact smallCMResidualQuotientMap_refl D V _
  map_comp f g := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D V _ _ _
      (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom g.unop))
      (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))).symm

local notation "groups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm

theorem cmHarrisLatticeCommonGroups_finite (k : ℕᵒᵖ) : Finite ((groups).obj k) :=
  smallCMResidualGroup_finite D V _

/-- The common quotient maps naturally to the residual groups for the V lattice. -/
def cmHarrisLatticeCommonOwnGroupMap : groups ⟶ ownGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D V _ _
    (cmHarrisLatticeCommonLevel_le_own D ρ p U V hVU m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

/-- The common quotient also maps naturally to the restricted original residual groups. -/
def cmHarrisLatticeCommonCoarseGroupMap : groups ⟶ coarseGroups where
  app k := GrpCat.ofHom (smallCMResidualQuotientMap D V _ _
    (cmHarrisLatticeCommonLevel_le_coarse D ρ p U V hVU m hm k.unop))
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

local notation "ownGroupMap" => cmHarrisLatticeCommonOwnGroupMap D ρ p U V hVU m hm
local notation "coarseGroupMap" => cmHarrisLatticeCommonCoarseGroupMap D ρ p U V hVU m hm

/-- The V lattice diagram with its action factored through the common residual groups. -/
def cmHarrisLatticeCommonOwnCoefficients : EquivariantDiagram groups (ModuleCat R) where
  obj := (ownCoefficients).obj
  ρ k := ((ownCoefficients).ρ k).comp ((ownGroupMap).app k).hom
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisTorsionSystem D ρ p V m).map f).comm g

/-- The original U lattice diagram, restricted to V and the same common residual groups. -/
def cmHarrisLatticeCommonOriginalCoefficients : EquivariantDiagram groups (ModuleCat R) where
  obj := (coarseCoefficients).obj
  ρ k := ((coarseCoefficients).ρ k).comp ((coarseGroupMap).app k).hom
  comm {i j} f g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisCoarseTorsionSystem D ρ p U V hVU m).map f).comm g

local notation "ownCommon" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "originalCommon" =>
  cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm

/-- Actual lattice inclusion gives a coherent equivariant comparison over the common kernels. -/
def cmHarrisLatticeCommonCoefficientInclusion : ownCommon ⟶ originalCommon where
  hom := Functor.whiskerRight (cmHarrisTorsionSystemInclusion D ρ p U V hVU m)
    (Action.forget (ModuleCat R) V.obj.subgroup)
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisTorsionSystemInclusion D ρ p U V hVU m).app k).comm g

/-- The common-kernel coefficient map is the reduction of the same ambient inclusion. -/
@[simp] theorem cmHarrisLatticeCommonCoefficientInclusion_mk (k : ℕᵒᵖ)
    (x : harrisLattice ρ p ordinaryV) :
    ((cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm).hom.app k).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (harrisLatticeInclusion ρ p ordinaryU ordinaryV ordinaryInclusion x) := rfl

/-- All original coefficient reductions commute with the constructed comparison. -/
@[reassoc] theorem cmHarrisLatticeCommonCoefficientInclusion_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownCommon).obj.map f ≫
        (cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm).hom.app j =
      (cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm).hom.app i ≫
        (originalCommon).obj.map f :=
  (cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm).hom.naturality f

end PEL.HarrisTaylorCMWeilLevel
end Langlands.Shimura
