import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientFlat
import Langlands.Cohomology.DivisibleSystem.Cokernel

/-! # The divisible system on original CM coefficient sheaves -/

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
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid

local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local notation "scalarIso" => cmHarrisCoefficientSystemScalarCokernelIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid
local notation "powerExact" => cmHarrisCoefficientPowerSequence_exact D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "annihilation" => cmHarrisCoefficientSystem_powSMul_eq_zero D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid

/-- The original transition to exponent `r` descends the complementary scalar power. -/
def cmHarrisCoefficientDivisibleInclusion {r s : ℕ} (hrs : r < s) :
    (system).obj (op r) ⟶ (system).obj (op s) :=
  (scalarIso (homOfLE hrs.le).op).inv ≫
    cokernel.desc (powSMul m r ((system).obj (op s)))
      (powSMul m (s - r) ((system).obj (op s)))
      (by rw [powSMul_comp_powSMul, Nat.add_sub_of_le hrs.le, annihilation])

local notation "inclusion" => cmHarrisCoefficientDivisibleInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The constructed inclusion is normalized by the existing original transition. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientDivisibleInclusion_normalization
    {r s : ℕ} (hrs : r < s) :
    (system).map (homOfLE hrs.le).op ≫ inclusion hrs =
      powSMul m (s - r) ((system).obj (op s)) := by
  rw [cmHarrisCoefficientDivisibleInclusion,
    ← cmHarrisCoefficientSystemScalarCokernelIso_π_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid (homOfLE hrs.le).op]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact cokernel.π_desc _ _ _

/-- Complementary-power exactness makes the original inclusion monic. -/
instance cmHarrisCoefficientDivisibleInclusion_mono {r s : ℕ} (hrs : r < s) :
    Mono (inclusion hrs) := by
  have hexactAt : ∀ t : ℕ, (heq : r + (s - r) = t) →
      (ShortComplex.mk (powSMul m r ((system).obj (op t)))
        (powSMul m (s - r) ((system).obj (op t)))
        (by rw [powSMul_comp_powSMul, heq, annihilation])).Exact := by
    rintro t rfl
    exact powerExact r (s - r)
  have hexact := hexactAt s (by omega)
  have := hexact.mono_cokernelDesc
  exact mono_comp _ _

/-- The inclusion is killed by the original complementary-exponent transition. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientDivisibleInclusion_comp
    {r s : ℕ} (hrs : r < s) :
    inclusion hrs ≫ (system).map (homOfLE (Nat.sub_le s r)).op = 0 := by
  rw [← cancel_epi ((system).map (homOfLE hrs.le).op), ← Category.assoc,
    cmHarrisCoefficientDivisibleInclusion_normalization, comp_zero]
  exact cmHarrisCoefficientSystem_scalar_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
    (homOfLE (Nat.sub_le s r)).op

/-- The original inclusion and complementary reduction form Harris's finite row. -/
def cmHarrisCoefficientDivisibleSequence {r s : ℕ} (hrs : r < s) :
    ShortComplex (Sheaf J (ModuleCat.{0} Rcoeff)) :=
  ShortComplex.mk (inclusion hrs) ((system).map (homOfLE (Nat.sub_le s r)).op)
    (cmHarrisCoefficientDivisibleInclusion_comp D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid hrs)

local notation "row" => cmHarrisCoefficientDivisibleSequence D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The scalar row maps to the original divisible row by reduction and two identities. -/
def cmHarrisCoefficientDivisibleSequenceComparison {r s : ℕ} (hrs : r < s) :
    cmHarrisCoefficientScalarSequence D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
      (homOfLE (Nat.sub_le s r)).op ⟶ row hrs where
  τ₁ := (system).map (homOfLE hrs.le).op
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change (system).map (homOfLE hrs.le).op ≫ inclusion hrs =
      powSMul m (s - r) ((system).obj (op s)) ≫ 𝟙 _
    rw [Category.comp_id]
    exact cmHarrisCoefficientDivisibleInclusion_normalization D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid hrs
  comm₂₃ := by
    change (𝟙 _) ≫ (system).map (homOfLE (Nat.sub_le s r)).op =
      (system).map (homOfLE (Nat.sub_le s r)).op ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- Exactness of the scalar row descends along its epimorphic first component. -/
theorem cmHarrisCoefficientDivisibleSequence_exact {r s : ℕ} (hrs : r < s) :
    (row hrs).Exact := by
  let φ := cmHarrisCoefficientDivisibleSequenceComparison D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid hrs
  have : Epi φ.τ₁ := cmHarrisCoefficientSystem_map_epi D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid (homOfLE hrs.le).op
  have : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 _); infer_instance
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
  exact cmHarrisCoefficientScalarSequence_exact D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
    (homOfLE (Nat.sub_le s r)).op

/-- The actual original finite rows are short exact in the small-etale sheaf category. -/
theorem cmHarrisCoefficientDivisibleSequence_shortExact {r s : ℕ} (hrs : r < s) :
    (row hrs).ShortExact :=
  { exact := cmHarrisCoefficientDivisibleSequence_exact D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid hrs
    mono_f := cmHarrisCoefficientDivisibleInclusion_mono D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid hrs
    epi_g := cmHarrisCoefficientSystem_map_epi D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid (homOfLE (Nat.sub_le s r)).op }

/-- The published generic constructor supplies the torsion condition on the unchanged tower. -/
def cmHarrisCoefficientDivisibleSystem : DivisibleSystem (Sheaf J (ModuleCat.{0} Rcoeff)) m :=
  DivisibleSystem.ofFlat system inclusion annihilation
    (cmHarrisCoefficientDivisibleInclusion_comp D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid)
    (cmHarrisCoefficientDivisibleSequence_shortExact D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid)
    powerExact

local notation "divisible" => cmHarrisCoefficientDivisibleSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The divisible system uses exactly the existing original coefficient tower. -/
@[simp] theorem cmHarrisCoefficientDivisibleSystem_tower : (divisible).tower = system := rfl

/-- Its inclusion is the normalized cokernel descent constructed above. -/
@[simp] theorem cmHarrisCoefficientDivisibleSystem_inclusion {r s : ℕ} (hrs : r < s) :
    (divisible).inclusion hrs = inclusion hrs := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
