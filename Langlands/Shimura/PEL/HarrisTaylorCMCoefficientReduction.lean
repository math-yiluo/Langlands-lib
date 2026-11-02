import Langlands.Shimura.Coefficients.HarrisCongruenceLevels
import Langlands.Shimura.PEL.HarrisTaylorCMNormalRefinement
import Mathlib.Algebra.Group.Equiv.Opposite

/-! # Full Harris coefficient reductions on the original opposite CM levels -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory

namespace Langlands.Shimura

namespace CompactOpenLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inversion identifies a topological group with its opposite as groups. -/
def inverseOppositeContinuousEquiv : G ≃ₜ* Gᵐᵒᵖ where
  toMulEquiv := MulEquiv.inv' G
  continuous_toFun := MulOpposite.continuous_op.comp continuous_inv
  continuous_invFun := continuous_inv.comp MulOpposite.continuous_unop

/-- The ordinary compact open level attached to an opposite level by inverse-unop. -/
def inverseOpposite (U : CompactOpenLevel Gᵐᵒᵖ) : CompactOpenLevel G where
  openSubgroup := U.openSubgroup.comap
    (inverseOppositeContinuousEquiv (G := G)).toMulEquiv.toMonoidHom
    (inverseOppositeContinuousEquiv (G := G)).continuous
  isCompact :=
    (inverseOppositeContinuousEquiv (G := G)).toHomeomorph.isCompact_preimage.mpr U.isCompact

@[simp] theorem mem_inverseOpposite (U : CompactOpenLevel Gᵐᵒᵖ) (g : G) :
    g ∈ (inverseOpposite U).subgroup ↔ MulOpposite.op g⁻¹ ∈ U.subgroup := Iff.rfl

/-- The level-group isomorphism sends an opposite element to inverse-unop. -/
def inverseOppositeEquiv (U : CompactOpenLevel Gᵐᵒᵖ) :
    U.subgroup ≃* (inverseOpposite U).subgroup where
  toFun g := ⟨(MulEquiv.inv' G).symm g, by
    change (MulEquiv.inv' G) ((MulEquiv.inv' G).symm g) ∈ U.subgroup
    simpa only [MulEquiv.apply_symm_apply] using g.property⟩
  invFun g := ⟨(MulEquiv.inv' G) g, g.property⟩
  left_inv g := Subtype.ext ((MulEquiv.inv' G).apply_symm_apply g)
  right_inv g := Subtype.ext ((MulEquiv.inv' G).symm_apply_apply g)
  map_mul' g h := Subtype.ext ((MulEquiv.inv' G).symm.map_mul g h)

@[simp] theorem inverseOppositeEquiv_coe (U : CompactOpenLevel Gᵐᵒᵖ)
    (g : U.subgroup) :
    (inverseOppositeEquiv U g : G) = (MulOpposite.unop (g : Gᵐᵒᵖ))⁻¹ := rfl

theorem continuous_inverseOppositeEquiv (U : CompactOpenLevel Gᵐᵒᵖ) :
    Continuous (inverseOppositeEquiv U) :=
  (continuous_inv.comp (MulOpposite.continuous_unop.comp continuous_subtype_val)).subtype_mk _

end CompactOpenLevel

namespace PEL.HarrisTaylorCMWeilLevel

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

/-- The full Harris lattice reduction with the original CM level as its acting group. -/
def cmHarrisFiniteTorsionAction (m k : ℕ) :
    Action (ModuleCat (HarrisCoefficientReductionRing K p m k)) U.obj.subgroup where
  V := (harrisFiniteTorsionAction ρ p ordinaryLevel m k).V
  ρ := (harrisFiniteTorsionAction ρ p ordinaryLevel m k).ρ.comp (levelEquiv).toMonoidHom

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem cmHarrisFiniteTorsionAction_ρ (m k : ℕ) (g : U.obj.subgroup) :
    (cmHarrisFiniteTorsionAction D ρ p U m k).ρ g =
      (harrisFiniteTorsionAction ρ p ordinaryLevel m k).ρ (levelEquiv g) := rfl

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- On lattice representatives the transported action is precisely the original inverse-unop action. -/
@[simp] theorem cmHarrisFiniteTorsionAction_mk (m k : ℕ) (g : U.obj.subgroup)
    (x : (harrisLatticeAction ρ p ordinaryLevel).V) :
    ((cmHarrisFiniteTorsionAction D ρ p U m k).ρ g).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((harrisLatticeAction ρ p ordinaryLevel).ρ
        (levelEquiv g)).hom x) := rfl

/-- The actual coefficient-action kernel in the original opposite CM level group. -/
def cmHarrisCongruenceKernel (m k : ℕ) : Subgroup U.obj.subgroup :=
  (cmHarrisFiniteTorsionAction D ρ p U m k).ρ.ker

instance cmHarrisCongruenceKernel_normal (m k : ℕ) :
    (cmHarrisCongruenceKernel D ρ p U m k).Normal :=
  MonoidHom.normal_ker _

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
theorem cmHarrisCongruenceKernel_eq (m k : ℕ) :
    cmHarrisCongruenceKernel D ρ p U m k =
      (harrisCongruenceKernel ρ p ordinaryLevel m k).comap (levelEquiv).toMonoidHom := by
  change ((harrisFiniteTorsionAction ρ p ordinaryLevel m k).ρ.comp
    (levelEquiv).toMonoidHom).ker = _
  rw [← MonoidHom.comap_ker, harrisFiniteTorsionAction_ker]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- The original CM kernel tests the full collection of coefficient places above p. -/
theorem mem_cmHarrisCongruenceKernel (m k : ℕ) (g : U.obj.subgroup) :
    g ∈ cmHarrisCongruenceKernel D ρ p U m k ↔
      ∀ l : AdelicFunctoriality.FinitePlacesAbove K p,
        levelEquiv g ∈ congruenceKernel (coefficientScalarIdeal l.1 m)
          (algebraicCompactCoefficientLattice ρ p l.1 ordinaryLevel).action k := by
  rw [cmHarrisCongruenceKernel_eq]
  exact mem_harrisCongruenceKernel ρ p ordinaryLevel m k (levelEquiv g)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
theorem cmHarrisCongruenceKernel_isOpen (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    IsOpen (cmHarrisCongruenceKernel D ρ p U m k : Set U.obj.subgroup) := by
  rw [cmHarrisCongruenceKernel_eq]
  exact (harrisCongruenceKernel_isOpen ρ p ordinaryLevel m hm k).preimage
    (CompactOpenLevel.continuous_inverseOppositeEquiv U.obj)

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
theorem cmHarrisFiniteTorsionAction_finite (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    Finite (cmHarrisFiniteTorsionAction D ρ p U m k).V :=
  harrisTorsionAction_finite ρ p ordinaryLevel m hm k

/-- The actual small CM level cut out by the full Harris coefficient kernel. -/
def cmHarrisCoefficientLevel (m : ℕ) (hm : m ≠ 0) (k : ℕ) : SmallCMLevel D :=
  ⟨U.obj.sublevel (cmHarrisCongruenceKernel D ρ p U m k)
      (cmHarrisCongruenceKernel_isOpen D ρ p U m hm k),
    U.property.mono (LevelSpace.sublevelSubgroup_le _ _)⟩

theorem cmHarrisCoefficientLevel_le (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup ≤ U.obj.subgroup :=
  LevelSpace.sublevelSubgroup_le _ _

/-- Restricting the constructed ambient level back to U recovers exactly the action kernel. -/
theorem cmHarrisCoefficientLevel_subgroupOf (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup.subgroupOf U.obj.subgroup =
      cmHarrisCongruenceKernel D ρ p U m k := by
  ext g
  change (g : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ∈
    (cmHarrisCongruenceKernel D ρ p U m k).map U.obj.subgroup.subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (Subtype.ext he : a = g) ▸ ha
  · intro hg
    exact ⟨g, hg, rfl⟩

instance cmHarrisCoefficientLevel_normal (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    ((cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup.subgroupOf
      U.obj.subgroup).Normal := by
  rw [cmHarrisCoefficientLevel_subgroupOf]
  infer_instance

variable (V : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

/-- Factor the full coefficient action through an original CM normal-level quotient. -/
def cmHarrisResidualCoefficientAction (m k : ℕ)
    (hker : V.obj.subgroup.subgroupOf U.obj.subgroup ≤
      cmHarrisCongruenceKernel D ρ p U m k) :
    Action (ModuleCat (HarrisCoefficientReductionRing K p m k))
      (SmallCMResidualGroup D U V) where
  V := (cmHarrisFiniteTorsionAction D ρ p U m k).V
  ρ := QuotientGroup.lift _ (cmHarrisFiniteTorsionAction D ρ p U m k).ρ hker

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
@[simp] theorem cmHarrisResidualCoefficientAction_mk (m k : ℕ)
    (hker : V.obj.subgroup.subgroupOf U.obj.subgroup ≤
      cmHarrisCongruenceKernel D ρ p U m k) (g : U.obj.subgroup) :
    (cmHarrisResidualCoefficientAction D ρ p U V m k hker).ρ (QuotientGroup.mk g) =
      (harrisFiniteTorsionAction ρ p ordinaryLevel m k).ρ (levelEquiv g) := rfl

/-- At the constructed coefficient level, factorization has no kernel-containment premise. -/
def cmHarrisCoefficientAction (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    Action (ModuleCat (HarrisCoefficientReductionRing K p m k))
      (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k)) :=
  cmHarrisResidualCoefficientAction D ρ p U
    (cmHarrisCoefficientLevel D ρ p U m hm k) m k
    (le_of_eq (cmHarrisCoefficientLevel_subgroupOf D ρ p U m hm k))

/-- This quotient is precisely the faithful finite image of the transported coefficient action. -/
theorem cmHarrisCoefficientAction_injective (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    Function.Injective (cmHarrisCoefficientAction D ρ p U m hm k).ρ :=
  (QuotientGroup.injective_lift_iff _
    (cmHarrisFiniteTorsionAction D ρ p U m k).ρ
    (le_of_eq (cmHarrisCoefficientLevel_subgroupOf D ρ p U m hm k))).mpr
    (cmHarrisCoefficientLevel_subgroupOf D ρ p U m hm k)

/-- Both the original CM quotient group and its actual full coefficient reduction are finite. -/
theorem cmHarrisCoefficientAction_finite (m : ℕ) (hm : m ≠ 0) (k : ℕ) :
    Finite (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k)) ∧
      Finite (cmHarrisCoefficientAction D ρ p U m hm k).V :=
  ⟨smallCMResidualGroup_finite D U _, cmHarrisFiniteTorsionAction_finite D ρ p U m hm k⟩

end PEL.HarrisTaylorCMWeilLevel
end Langlands.Shimura
