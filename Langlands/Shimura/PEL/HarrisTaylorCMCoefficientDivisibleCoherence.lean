import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDivisible

/-! # Coherent inclusions on the original CM coefficient sheaves -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
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

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "X" => Functor.obj (schemes q) U
local notation "J" => Scheme.smallEtaleTopology X
local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local notation "scalarIso" => cmHarrisCoefficientSystemScalarCokernelIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid
local notation "annihilation" => cmHarrisCoefficientSystem_powSMul_eq_zero D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid

/-- The normalized cokernel inclusion also makes sense for equal exponents. -/
def cmHarrisCoefficientInclusionLE {r s : ℕ} (hrs : r ≤ s) :
    (system).obj (op r) ⟶ (system).obj (op s) :=
  (scalarIso (homOfLE hrs).op).inv ≫
    cokernel.desc (powSMul m r ((system).obj (op s)))
      (powSMul m (s - r) ((system).obj (op s)))
      (by rw [powSMul_comp_powSMul, Nat.add_sub_of_le hrs, annihilation])

local notation "inclusionLE" => cmHarrisCoefficientInclusionLE D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- For strict inequalities this is exactly the published original inclusion. -/
@[simp] theorem cmHarrisCoefficientInclusionLE_of_lt {r s : ℕ} (hrs : r < s) :
    inclusionLE hrs.le = cmHarrisCoefficientDivisibleInclusion D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid hrs := rfl

/-- Normalization fixes the inclusion relative to the original reduction. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientInclusionLE_normalization
    {r s : ℕ} (hrs : r ≤ s) :
    (system).map (homOfLE hrs).op ≫ inclusionLE hrs =
      powSMul m (s - r) ((system).obj (op s)) := by
  rw [cmHarrisCoefficientInclusionLE,
    ← cmHarrisCoefficientSystemScalarCokernelIso_π_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid (homOfLE hrs).op]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact cokernel.π_desc _ _ _

/-- An original reduction is an epimorphism, so its normalization determines a map. -/
theorem cmHarrisCoefficientInclusionLE_unique {r s : ℕ} (hrs : r ≤ s)
    (f : (system).obj (op r) ⟶ (system).obj (op s))
    (hf : (system).map (homOfLE hrs).op ≫ f =
      powSMul m (s - r) ((system).obj (op s))) : f = inclusionLE hrs := by
  rw [← cancel_epi ((system).map (homOfLE hrs).op), hf,
    cmHarrisCoefficientInclusionLE_normalization]

/-- Equal-exponent normalized inclusion is the identity. -/
@[simp] theorem cmHarrisCoefficientInclusionLE_refl (r : ℕ) :
    inclusionLE (le_refl r) = 𝟙 _ := by
  have hn := cmHarrisCoefficientInclusionLE_normalization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid (le_refl r)
  simpa only [show (homOfLE (le_refl r)).op = 𝟙 (op r) from Subsingleton.elim _ _,
    (system).map_id, Category.id_comp, Nat.sub_self, powSMul_zero] using hn

/-- Normalization also gives scalar multiplication in the reverse order. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientInclusionLE_reduction
    {r s : ℕ} (hrs : r ≤ s) :
    inclusionLE hrs ≫ (system).map (homOfLE hrs).op =
      powSMul m (s - r) ((system).obj (op r)) := by
  rw [← cancel_epi ((system).map (homOfLE hrs).op),
    ← Category.assoc, cmHarrisCoefficientInclusionLE_normalization, comp_powSMul]

/-- The existing inverse system composes the specified reduction arrows. -/
@[reassoc] theorem cmHarrisCoefficientReduction_trans {r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (system).map (homOfLE hst).op ≫ (system).map (homOfLE hrs).op =
      (system).map (homOfLE (hrs.trans hst)).op := by
  rw [← Functor.map_comp]
  congr 1

/-- Normalized inclusions compose on the original sheaves. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientInclusionLE_trans {r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) :
    inclusionLE hrs ≫ inclusionLE hst = inclusionLE (hrs.trans hst) := by
  rw [← cancel_epi ((system).map (homOfLE (hrs.trans hst)).op),
    cmHarrisCoefficientInclusionLE_normalization,
    ← cmHarrisCoefficientReduction_trans D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
      hrs hst,
    Category.assoc, ← Category.assoc ((system).map (homOfLE hrs).op),
    cmHarrisCoefficientInclusionLE_normalization,
    ← Category.assoc, comp_powSMul, Category.assoc,
    cmHarrisCoefficientInclusionLE_normalization, powSMul_comp_powSMul]
  congr 1
  omega

/-- The same coefficient sheaves form a direct system under normalized inclusions. -/
def cmHarrisCoefficientDirectSystem : ℕ ⥤ Sheaf J (ModuleCat.{0} Rcoeff) where
  obj r := (system).obj (op r)
  map f := inclusionLE (leOfHom f)
  map_id r := cmHarrisCoefficientInclusionLE_refl D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid r
  map_comp f g := (cmHarrisCoefficientInclusionLE_trans D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid (leOfHom f) (leOfHom g)).symm

/-- Every map in the resulting direct system is monic. -/
instance cmHarrisCoefficientInclusionLE_mono {r s : ℕ} (hrs : r ≤ s) :
    Mono (inclusionLE hrs) := by
  rcases lt_or_eq_of_le hrs with hlt | rfl
  · change Mono (cmHarrisCoefficientDivisibleInclusion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid hlt)
    infer_instance
  · rw [cmHarrisCoefficientInclusionLE_refl]
    infer_instance

/-- In particular the published strict inclusions satisfy the composition law. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientDivisibleInclusion_trans
    {r s t : ℕ} (hrs : r < s) (hst : s < t) :
    cmHarrisCoefficientDivisibleInclusion D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid hrs ≫
    cmHarrisCoefficientDivisibleInclusion D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid hst =
    cmHarrisCoefficientDivisibleInclusion D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
      (hrs.trans hst) :=
  cmHarrisCoefficientInclusionLE_trans D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
    hrs.le hst.le

/-- Shifting both exponents by the same amount gives the original mixed square. -/
@[reassoc] theorem cmHarrisCoefficientInclusionLE_shift_naturality
    {r s : ℕ} (hsr : s ≤ r) (k : ℕ) :
    inclusionLE (Nat.le_add_right r k) ≫
        (system).map (homOfLE (Nat.add_le_add_right hsr k)).op =
      (system).map (homOfLE hsr).op ≫ inclusionLE (Nat.le_add_right s k) := by
  have hfactor :
      (system).map (homOfLE (Nat.le_add_right r k)).op ≫
          (system).map (homOfLE hsr).op =
        (system).map (homOfLE (Nat.add_le_add_right hsr k)).op ≫
          (system).map (homOfLE (Nat.le_add_right s k)).op := by
    rw [cmHarrisCoefficientReduction_trans, cmHarrisCoefficientReduction_trans]
  rw [← cancel_epi ((system).map (homOfLE (Nat.le_add_right r k)).op),
    ← Category.assoc, cmHarrisCoefficientInclusionLE_normalization,
    Nat.add_sub_cancel_left,
    ← Category.assoc ((system).map (homOfLE (Nat.le_add_right r k)).op),
    hfactor, Category.assoc, cmHarrisCoefficientInclusionLE_normalization,
    Nat.add_sub_cancel_left]
  exact (comp_powSMul m k ((system).map (homOfLE (Nat.add_le_add_right hsr k)).op)).symm

/-- Reindex the existing inverse system by the original exponents plus `k`. -/
def cmHarrisCoefficientShiftedSystem (k : ℕ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} Rcoeff) :=
  (show Monotone (fun r : ℕ => r + k) from
    fun _ _ hrs => Nat.add_le_add_right hrs k).functor.op ⋙ system

local notation "shifted" => cmHarrisCoefficientShiftedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Normalized inclusions give a morphism to every shifted original inverse system. -/
def cmHarrisCoefficientShiftInclusion (k : ℕ) : system ⟶ shifted k where
  app r := inclusionLE (Nat.le_add_right r.unop k)
  naturality r s f := by
    change (system).map f ≫ inclusionLE (Nat.le_add_right s.unop k) =
      inclusionLE (Nat.le_add_right r.unop k) ≫
        (system).map (homOfLE (Nat.add_le_add_right (leOfHom f.unop) k)).op
    simpa only [show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
      (cmHarrisCoefficientInclusionLE_shift_naturality D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid (leOfHom f.unop) k).symm

/-- Original reductions give the morphism back from the shifted inverse system. -/
def cmHarrisCoefficientShiftReduction (k : ℕ) : shifted k ⟶ system where
  app r := (system).map (homOfLE (Nat.le_add_right r.unop k)).op
  naturality r s f := by
    change (system).map _ ≫ (system).map _ = (system).map _ ≫ (system).map _
    rw [← (system).map_comp, ← (system).map_comp]
    congr 1

local notation "shiftInclusion" => cmHarrisCoefficientShiftInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "shiftReduction" => cmHarrisCoefficientShiftReduction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The composite on the original inverse system is multiplication by `m^k`. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientShiftInclusion_reduction (k : ℕ) :
    shiftInclusion k ≫ shiftReduction k = powSMul m k system := by
  apply NatTrans.ext
  funext r
  change inclusionLE (Nat.le_add_right r.unop k) ≫
    (system).map (homOfLE (Nat.le_add_right r.unop k)).op =
      powSMul m k ((system).obj r)
  rw [cmHarrisCoefficientInclusionLE_reduction, Nat.add_sub_cancel_left]

/-- The opposite composite is the same scalar on the shifted inverse system. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientShiftReduction_inclusion (k : ℕ) :
    shiftReduction k ≫ shiftInclusion k = powSMul m k (shifted k) := by
  apply NatTrans.ext
  funext r
  change (system).map (homOfLE (Nat.le_add_right r.unop k)).op ≫
    inclusionLE (Nat.le_add_right r.unop k) =
      powSMul m k ((system).obj (op (r.unop + k)))
  rw [cmHarrisCoefficientInclusionLE_normalization, Nat.add_sub_cancel_left]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
