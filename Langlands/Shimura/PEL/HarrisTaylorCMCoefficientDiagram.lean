import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientReduction

/-! # Exponent diagrams on the original CM coefficient levels -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory Opposite

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.Global Langlands.Shimura.Coefficients

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {d : ℕ} (D : CentralSimpleUnitaryData E F A d)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (U : SmallCMLevel D)

local notation "ordinaryLevel" => CompactOpenLevel.inverseOpposite U.obj
local notation "levelEquiv" => CompactOpenLevel.inverseOppositeEquiv U.obj

/-- The full Harris torsion system transported to the original opposite CM level group. -/
def cmHarrisTorsionSystem (m : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat (HarrisCoefficientIntegers K p)) U.obj.subgroup :=
  harrisTorsionSystem ρ p ordinaryLevel m ⋙
    Action.res (ModuleCat (HarrisCoefficientIntegers K p)) (levelEquiv).toMonoidHom

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Integral scalars retain exactly the carrier of the published full quotient-ring action. -/
theorem cmHarrisTorsionSystem_obj_carrier (m k : ℕ) :
    ((cmHarrisTorsionSystem D ρ p U m).obj (op k)).V.carrier =
      (cmHarrisFiniteTorsionAction D ρ p U m k).V.carrier := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Retaining integral scalars leaves the actual CM coefficient kernel unchanged. -/
theorem cmHarrisTorsionSystem_ker (m k : ℕ) :
    ((cmHarrisTorsionSystem D ρ p U m).obj (op k)).ρ.ker =
      cmHarrisCongruenceKernel D ρ p U m k := by
  rw [cmHarrisCongruenceKernel_eq]
  change ((harrisTorsionAction ρ p ordinaryLevel m k).ρ.comp
    (levelEquiv).toMonoidHom).ker = _
  rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Higher full coefficient powers cut out smaller actual CM kernels. -/
theorem cmHarrisCongruenceKernel_antitone (m : ℕ) :
    Antitone (cmHarrisCongruenceKernel D ρ p U m) := by
  intro i j hij
  rw [cmHarrisCongruenceKernel_eq, cmHarrisCongruenceKernel_eq]
  exact Subgroup.comap_mono (congruenceKernel_antitone
    (harrisCoefficientScalarIdeal K p m) (harrisLatticeAction ρ p ordinaryLevel) hij)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The ambient small CM coefficient levels inherit the proved kernel inclusions. -/
theorem cmHarrisCoefficientLevel_antitone (m : ℕ) (hm : m ≠ 0) :
    Antitone (fun k => (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup) := by
  intro i j hij
  exact LevelSpace.sublevelSubgroup_mono U.obj.subgroup
    (cmHarrisCongruenceKernel_antitone D ρ p U m hij)

/-- Genuine inverse diagram of the actual small CM coefficient levels. -/
def cmHarrisCoefficientLevels (m : ℕ) (hm : m ≠ 0) : ℕᵒᵖ ⥤ SmallCMLevel D where
  obj k := cmHarrisCoefficientLevel D ρ p U m hm k.unop
  map f := smallCMInclusion D (cmHarrisCoefficientLevel_antitone D ρ p U m hm
    (leOfHom f.unop))
  map_id _ := smallCMInclusion_refl D _
  map_comp _ _ := (smallCMInclusion_trans D _ _).symm

/-- The level diagram carries its canonical natural inclusion into the original level. -/
def cmHarrisCoefficientLevelProjection (m : ℕ) (hm : m ≠ 0) :
    cmHarrisCoefficientLevels D ρ p U m hm ⟶ (Functor.const ℕᵒᵖ).obj U where
  app k := smallCMInclusion D (cmHarrisCoefficientLevel_le D ρ p U m hm k.unop)
  naturality i j f := by
    dsimp [cmHarrisCoefficientLevels]
    rw [Category.comp_id, smallCMInclusion_trans]

/-- The actual residual groups of these original CM levels, with identity-induced maps. -/
def cmHarrisCoefficientGroups (m : ℕ) (hm : m ≠ 0) : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of
    (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k.unop))
  map f := GrpCat.ofHom (smallCMResidualQuotientMap D U _ _
    (cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom f.unop)))
  map_id k := by
    apply GrpCat.hom_ext
    exact smallCMResidualQuotientMap_refl D U _
  map_comp f g := by
    apply GrpCat.hom_ext
    exact (smallCMResidualQuotientMap_comp D U _ _ _
      (cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom g.unop))
      (cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom f.unop))).symm

/-- Every group transition retains the original representative in the opposite CM level. -/
@[simp] theorem cmHarrisCoefficientGroups_map_mk (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) (g : U.obj.subgroup) :
    ((cmHarrisCoefficientGroups D ρ p U m hm).map f).hom (QuotientGroup.mk g) =
      QuotientGroup.mk g := rfl

/-- The actual CM residual group transitions are surjective. -/
theorem cmHarrisCoefficientGroups_map_surjective (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((cmHarrisCoefficientGroups D ρ p U m hm).map f).hom :=
  smallCMResidualQuotientMap_surjective D U _ _
    (cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom f.unop))

/-- Every group in this actual CM diagram is finite. -/
theorem cmHarrisCoefficientGroups_finite (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    Finite ((cmHarrisCoefficientGroups D ρ p U m hm).obj k) :=
  smallCMResidualGroup_finite D U _

/-- Full Harris reductions form an equivariant diagram over the actual CM residual groups. -/
def cmHarrisCoefficientDiagram (m : ℕ) (hm : m ≠ 0) :
    EquivariantDiagram (cmHarrisCoefficientGroups D ρ p U m hm)
      (ModuleCat (HarrisCoefficientIntegers K p)) where
  obj := cmHarrisTorsionSystem D ρ p U m ⋙
    Action.forget (ModuleCat (HarrisCoefficientIntegers K p)) U.obj.subgroup
  ρ k := QuotientGroup.lift _ ((cmHarrisTorsionSystem D ρ p U m).obj k).ρ (by
    rw [cmHarrisTorsionSystem_ker, cmHarrisCoefficientLevel_subgroupOf])
  comm := by
    intro i j f g
    induction g using QuotientGroup.induction_on with
    | H g => exact ((cmHarrisTorsionSystem D ρ p U m).map f).comm g

/-- Forgetting residual actions gives exactly the transported full torsion system. -/
@[simp] theorem cmHarrisCoefficientDiagram_obj (m : ℕ) (hm : m ≠ 0) :
    (cmHarrisCoefficientDiagram D ρ p U m hm).obj =
      cmHarrisTorsionSystem D ρ p U m ⋙
        Action.forget (ModuleCat (HarrisCoefficientIntegers K p)) U.obj.subgroup := rfl

/-- At each index, the carrier is the original full quotient-ring coefficient carrier. -/
theorem cmHarrisCoefficientDiagram_obj_carrier (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    ((cmHarrisCoefficientDiagram D ρ p U m hm).obj.obj (op k)).carrier =
      (cmHarrisCoefficientAction D ρ p U m hm k).V.carrier := rfl

/-- Its residual action agrees pointwise with the published full quotient-ring action. -/
theorem cmHarrisCoefficientDiagram_action (m : ℕ) (hm : m ≠ 0) (k : ℕ)
    (g : SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k))
    (x : ((cmHarrisTorsionSystem D ρ p U m).obj (op k)).V) :
    ((cmHarrisCoefficientDiagram D ρ p U m hm).ρ (op k) g).hom x =
      ((cmHarrisCoefficientAction D ρ p U m hm k).ρ g).hom x := by
  induction g using QuotientGroup.induction_on with
  | H g => rfl

/-- On lattice representatives the residual action retains the inverse-unop convention. -/
@[simp] theorem cmHarrisCoefficientDiagram_action_mk (m : ℕ) (hm : m ≠ 0) (k : ℕ)
    (g : U.obj.subgroup) (x : (harrisLatticeAction ρ p ordinaryLevel).V) :
    ((cmHarrisCoefficientDiagram D ρ p U m hm).ρ (op k) (QuotientGroup.mk g)).hom
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((harrisLatticeAction ρ p ordinaryLevel).ρ
        (levelEquiv g)).hom x) := rfl

/-- Coefficient transitions are the canonical reductions, retaining the lattice representative. -/
@[simp] theorem cmHarrisCoefficientDiagram_transition_mk (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) (x : (harrisLatticeAction ρ p ordinaryLevel).V) :
    ((cmHarrisCoefficientDiagram D ρ p U m hm).transition f).hom.hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- All coefficient transitions are surjective full-lattice reductions. -/
theorem cmHarrisCoefficientDiagram_transition_surjective (m : ℕ) (hm : m ≠ 0)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((cmHarrisCoefficientDiagram D ρ p U m hm).transition f).hom :=
  harrisTorsionSystem_transition_surjective ρ p ordinaryLevel m (leOfHom f.unop)

/-- Each coefficient module in the diagram has a finite carrier. -/
theorem cmHarrisCoefficientDiagram_finite (m : ℕ) (hm : m ≠ 0) (k : ℕᵒᵖ) :
    Finite ((cmHarrisCoefficientDiagram D ρ p U m hm).obj.obj k) :=
  harrisTorsionAction_finite ρ p ordinaryLevel m hm k.unop

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
