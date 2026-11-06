import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCommonRefinement
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDiagram

/-! # Original Harris lattice coefficients restricted to smaller coarse CM levels -/

noncomputable section

open CategoryTheory Opposite

set_option autoImplicit false
set_option maxHeartbeats 800000

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
  (p : Global.FinitePlace ℚ) (U V : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup)

local notation "R" => HarrisCoefficientIntegers K p
local notation "originalLevel" m:arg hm:arg k:arg => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "originalLevels" m:arg hm:arg => cmHarrisCoefficientLevels D ρ p U m hm
local notation "originalGroups" m:arg hm:arg => cmHarrisCoefficientGroups D ρ p U m hm
local notation "originalCoefficients" m:arg hm:arg => cmHarrisCoefficientDiagram D ρ p U m hm

/-- Restrict the original full-lattice action without choosing a new lattice at V. -/
def cmHarrisCoarseTorsionSystem (m : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat R) V.obj.subgroup :=
  cmHarrisTorsionSystem D ρ p U m ⋙
    Action.res (ModuleCat R) (Subgroup.inclusion hVU)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Its action kernel is the actual inverse image of the original kernel. -/
theorem cmHarrisCoarseTorsionSystem_ker (m k : ℕ) :
    ((cmHarrisCoarseTorsionSystem D ρ p U V hVU m).obj (op k)).ρ.ker =
      (cmHarrisCongruenceKernel D ρ p U m k).comap (Subgroup.inclusion hVU) := by
  change (((cmHarrisTorsionSystem D ρ p U m).obj (op k)).ρ.comp
    (Subgroup.inclusion hVU)).ker = _
  rw [← MonoidHom.comap_ker, cmHarrisTorsionSystem_ker]

/-- The new kernel level is the original identity-Hecke intersection V ∩ U_k. -/
def cmHarrisCoarseCoefficientLevel (_hVU : V.obj.subgroup ≤ U.obj.subgroup) (m : ℕ) (hm : m ≠ 0) (k : ℕ) : SmallCMLevel D :=
  smallCMCommonLevel D V (originalLevel m hm k)

local notation "coarseLevel" m:arg hm:arg k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k

omit [IsCMField F] [IsScalarTower E F A] in
@[simp] theorem cmHarrisCoarseCoefficientLevel_subgroup (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (coarseLevel m hm k).obj.subgroup =
      V.obj.subgroup ⊓ (originalLevel m hm k).obj.subgroup :=
  smallCMCommonLevel_subgroup D V (originalLevel m hm k)

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmHarrisCoarseCoefficientLevel_le_coarse (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (coarseLevel m hm k).obj.subgroup ≤ V.obj.subgroup :=
  smallCMCommonLevel_le_left D V (originalLevel m hm k)

omit [IsCMField F] [IsScalarTower E F A] in
theorem cmHarrisCoarseCoefficientLevel_le_original (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (coarseLevel m hm k).obj.subgroup ≤ (originalLevel m hm k).obj.subgroup :=
  smallCMCommonLevel_le_right D V (originalLevel m hm k)

/-- Restriction to V recovers precisely the kernel of the original restricted action. -/
theorem cmHarrisCoarseCoefficientLevel_subgroupOf (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (coarseLevel m hm k).obj.subgroup.subgroupOf V.obj.subgroup =
      (cmHarrisCongruenceKernel D ρ p U m k).comap (Subgroup.inclusion hVU) := by
  ext g
  change (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
    (coarseLevel m hm k).obj.subgroup ↔ _
  rw [cmHarrisCoarseCoefficientLevel_subgroup]
  constructor
  · intro hg
    change Subgroup.inclusion hVU g ∈ cmHarrisCongruenceKernel D ρ p U m k
    rw [← cmHarrisCoefficientLevel_subgroupOf D ρ p U m hm k]
    exact hg.2
  · intro hg
    refine ⟨g.property, ?_⟩
    change Subgroup.inclusion hVU g ∈
      (originalLevel m hm k).obj.subgroup.subgroupOf U.obj.subgroup
    rw [cmHarrisCoefficientLevel_subgroupOf]
    exact hg

/-- The actual intersection level cuts out exactly the restricted full action kernel. -/
theorem cmHarrisCoarseCoefficientLevel_eq_ker (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (coarseLevel m hm k).obj.subgroup.subgroupOf V.obj.subgroup =
      ((cmHarrisCoarseTorsionSystem D ρ p U V hVU m).obj (op k)).ρ.ker := by
  rw [cmHarrisCoarseCoefficientLevel_subgroupOf, cmHarrisCoarseTorsionSystem_ker]

/-- No normality premise on V inside U is needed. -/
instance cmHarrisCoarseCoefficientLevel_normal (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    ((coarseLevel m hm k).obj.subgroup.subgroupOf V.obj.subgroup).Normal := by
  rw [cmHarrisCoarseCoefficientLevel_subgroupOf D ρ p U V hVU]
  infer_instance

omit [IsCMField F] [IsScalarTower E F A] in
/-- Higher exponents give smaller intersection levels. -/
theorem cmHarrisCoarseCoefficientLevel_antitone (m : ℕ) (hm : m ≠ 0) :
    Antitone (fun k => (coarseLevel m hm k).obj.subgroup) := by
  intro i j hij
  change (coarseLevel m hm j).obj.subgroup ≤ (coarseLevel m hm i).obj.subgroup
  rw [cmHarrisCoarseCoefficientLevel_subgroup, cmHarrisCoarseCoefficientLevel_subgroup]
  exact inf_le_inf_left _ (cmHarrisCoefficientLevel_antitone D ρ p U m hm hij)

/-- The actual restricted kernel levels, with original identity-transporter inclusions. -/
def cmHarrisCoarseCoefficientLevels (m : ℕ) (hm : m ≠ 0) : ℕᵒᵖ ⥤ SmallCMLevel D where
  obj k := coarseLevel m hm k.unop
  map f := smallCMInclusion D
    (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))
  map_id _ := smallCMInclusion_refl D _
  map_comp _ _ := (smallCMInclusion_trans D _ _).symm

local notation "coarseLevels" m:arg hm:arg => cmHarrisCoarseCoefficientLevels D ρ p U V hVU m hm

/-- The intersections project to the new coarse level by original inclusions. -/
def cmHarrisCoarseCoefficientLevelProjection (m : ℕ) (hm : m ≠ 0) :
    coarseLevels m hm ⟶ (Functor.const ℕᵒᵖ).obj V where
  app k := smallCMInclusion D
    (cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U V hVU m hm k.unop)
  naturality i j f := by
    dsimp [cmHarrisCoarseCoefficientLevels]
    rw [Category.comp_id, smallCMInclusion_trans]

/-- Their maps to the original kernel levels retain the actual intersection inclusions. -/
def cmHarrisCoarseCoefficientLevelComparison (m : ℕ) (hm : m ≠ 0) :
    coarseLevels m hm ⟶ originalLevels m hm where
  app k := smallCMInclusion D
    (cmHarrisCoarseCoefficientLevel_le_original D ρ p U V hVU m hm k.unop)
  naturality i j f := by
    dsimp [cmHarrisCoarseCoefficientLevels, cmHarrisCoefficientLevels]
    rw [smallCMInclusion_trans, smallCMInclusion_trans]

/-- Both actual routes from the intersection tower to U agree. -/
@[reassoc] theorem cmHarrisCoarseCoefficientLevelComparison_projection
    (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    (cmHarrisCoarseCoefficientLevelComparison D ρ p U V hVU m hm).app k ≫
        (cmHarrisCoefficientLevelProjection D ρ p U m hm).app k =
      (cmHarrisCoarseCoefficientLevelProjection D ρ p U V hVU m hm).app k ≫
        smallCMInclusion D hVU := by
  dsimp [cmHarrisCoarseCoefficientLevelComparison, cmHarrisCoarseCoefficientLevelProjection,
    cmHarrisCoefficientLevelProjection, cmHarrisCoarseCoefficientLevels, cmHarrisCoefficientLevels]
  rw [smallCMInclusion_trans, smallCMInclusion_trans]

/-- Residual groups of the actual intersection levels over V. -/
def cmHarrisCoarseCoefficientGroups (m : ℕ) (hm : m ≠ 0) : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of (SmallCMResidualGroup D V (coarseLevel m hm k.unop))
  map f := GrpCat.ofHom (smallCMResidualQuotientMap D V _ _
    (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop)))
  map_id k := by
    apply GrpCat.hom_ext
    exact smallCMResidualQuotientMap_refl D V _
  map_comp f g := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D V _ _ _
      (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom g.unop))
      (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))).symm

local notation "coarseGroups" m:arg hm:arg => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm

/-- Exponent quotient maps preserve the original representative in V. -/
@[simp] theorem cmHarrisCoarseCoefficientGroups_map_mk (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) (g : V.obj.subgroup) :
    ((coarseGroups m hm).map f).hom (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

/-- Every residual exponent transition is surjective. -/
theorem cmHarrisCoarseCoefficientGroups_map_surjective (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((coarseGroups m hm).map f).hom :=
  smallCMResidualQuotientMap_surjective D V _ _
    (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))

/-- Inclusion of V in U induces the original residual-group map at every exponent. -/
def cmHarrisCoarseCoefficientGroupInclusion (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    (coarseGroups m hm).obj k →* (originalGroups m hm).obj k :=
  QuotientGroup.quotientMapSubgroupOfOfLe
    (cmHarrisCoarseCoefficientLevel_le_original D ρ p U V hVU m hm k.unop) hVU

@[simp] theorem cmHarrisCoarseCoefficientGroupInclusion_mk
    (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) (g : V.obj.subgroup) :
    cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k (QuotientGroup.mk g) =
      QuotientGroup.mk (Subgroup.inclusion hVU g) := rfl

/-- The residual map is an embedding, rather than a surjectivity assertion. -/
theorem cmHarrisCoarseCoefficientGroupInclusion_injective
    (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    Function.Injective (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
    intro hg
    apply (QuotientGroup.eq_one_iff _).mpr
    change (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
      (coarseLevel m hm k.unop).obj.subgroup
    rw [cmHarrisCoarseCoefficientLevel_subgroup]
    refine ⟨g.property, ?_⟩
    change (QuotientGroup.mk (Subgroup.inclusion hVU g) :
      SmallCMResidualGroup D U (originalLevel m hm k.unop)) = 1 at hg
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hVU g)).mp hg

/-- Residual inclusions commute with all original exponent quotient maps. -/
def cmHarrisCoarseCoefficientGroupMap (m : ℕ) (hm : m ≠ 0) :
    coarseGroups m hm ⟶ originalGroups m hm where
  app k := GrpCat.ofHom (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k)
  naturality i j f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H g => rfl

/-- The finite groups are the actual compact/open residual quotients. -/
theorem cmHarrisCoarseCoefficientGroups_finite
    (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    Finite ((coarseGroups m hm).obj k) := smallCMResidualGroup_finite D V _

/-- The full original coefficient modules, with residual actions restricted along
those constructed embeddings and with all original lattice reductions retained. -/
def cmHarrisCoarseCoefficientDiagram (m : ℕ) (hm : m ≠ 0) :
    EquivariantDiagram (coarseGroups m hm) (ModuleCat R) where
  obj := (originalCoefficients m hm).obj
  ρ k := ((originalCoefficients m hm).ρ k).comp
    (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k)
  comm {i j} f g := by
    have he := congrArg (fun t => t.hom g)
      ((cmHarrisCoarseCoefficientGroupMap D ρ p U V hVU m hm).naturality f)
    change cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm j
        (((coarseGroups m hm).map f).hom g) =
      ((originalGroups m hm).map f).hom
        (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm i g) at he
    change (originalCoefficients m hm).ρ i
        (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm i g) ≫
        (originalCoefficients m hm).obj.map f =
      (originalCoefficients m hm).obj.map f ≫ (originalCoefficients m hm).ρ j _
    rw [he]
    exact (originalCoefficients m hm).comm f _

local notation "coarseCoefficients" m:arg hm:arg =>
  cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm

/-- Restriction changes no underlying coefficient module or reduction morphism. -/
@[simp] theorem cmHarrisCoarseCoefficientDiagram_obj (m : ℕ) (hm : m ≠ 0) :
    (coarseCoefficients m hm).obj = (originalCoefficients m hm).obj := rfl

/-- At every exponent this is exactly the original coefficient action restricted
through the constructed residual embedding. -/
def cmHarrisCoarseCoefficientActionIso (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    (Action.res (ModuleCat R)
      (cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k)).obj
        ((originalCoefficients m hm).action k) ≅ (coarseCoefficients m hm).action k :=
  Iso.refl _

/-- Pulling back the residual action to V recovers the original restricted torsion action. -/
@[simp] theorem cmHarrisCoarseCoefficientDiagram_action (m : ℕ) (hm : m ≠ 0)
    (k : ℕᵒᵖ) (g : V.obj.subgroup) :
    (coarseCoefficients m hm).ρ k (QuotientGroup.mk g) =
      ((cmHarrisCoarseTorsionSystem D ρ p U V hVU m).obj k).ρ g := rfl

/-- Original lattice representatives retain their inverse-unop action convention. -/
@[simp] theorem cmHarrisCoarseCoefficientDiagram_action_mk
    (m : ℕ) (hm : m ≠ 0) (k : ℕ) (g : V.obj.subgroup)
    (x : (harrisLatticeAction ρ p (CompactOpenLevel.inverseOpposite U.obj)).V) :
    ((coarseCoefficients m hm).ρ (op k) (QuotientGroup.mk g)).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (((harrisLatticeAction ρ p (CompactOpenLevel.inverseOpposite U.obj)).ρ
          (CompactOpenLevel.inverseOppositeEquiv U.obj (Subgroup.inclusion hVU g))).hom x) := rfl

/-- Every exponent transition is the original full-lattice representative reduction. -/
@[simp] theorem cmHarrisCoarseCoefficientDiagram_transition_mk
    (m : ℕ) (hm : m ≠ 0) {i j : ℕᵒᵖ} (f : i ⟶ j)
    (x : (harrisLatticeAction ρ p (CompactOpenLevel.inverseOpposite U.obj)).V) :
    ((coarseCoefficients m hm).transition f).hom.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

/-- Coefficient carriers remain finite full-lattice quotients. -/
theorem cmHarrisCoarseCoefficientDiagram_finite
    (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    Finite ((coarseCoefficients m hm).obj.obj k) :=
  cmHarrisCoefficientDiagram_finite D ρ p U m hm k

/-- Every coefficient transition is still surjective. -/
theorem cmHarrisCoarseCoefficientDiagram_transition_surjective
    (m : ℕ) (hm : m ≠ 0) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((coarseCoefficients m hm).transition f).hom :=
  cmHarrisCoefficientDiagram_transition_surjective D ρ p U m hm f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
