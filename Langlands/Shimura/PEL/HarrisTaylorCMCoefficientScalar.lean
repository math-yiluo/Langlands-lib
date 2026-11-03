import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Scalar cokernels of original CM coefficient reductions -/

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
open Langlands.Shimura.Coefficients

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

variable {i j : ℕᵒᵖ} (f : i ⟶ j)
local notation "φ" => (coefficients).transition f
local notation "Fassoc" => etaleAssociatedFunctor (R := Rcoeff) X ((covers).action i)

/-- Scalar multiplication on the original fine action is killed by reduction. -/
theorem cmHarrisCoefficientDiagram_scalar_comp :
    ((m ^ j.unop) • (𝟙 ((coefficients).action i))) ≫ φ = 0 := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Submodule.Quotient.mk ((m ^ j.unop) • y) :
    ((coefficients).action j).V) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (mem_principalPower_smul_top (m : Rcoeff) j.unop _).mpr
  exact ⟨y, by simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

/-- Scalar multiplication followed by the actual full-lattice reduction. -/
def cmHarrisCoefficientScalarActionSequence :
    ShortComplex (Action (ModuleCat.{0} Rcoeff)
      ((cmHarrisCoefficientGroups D ρ p U m hm).obj i)) :=
  ShortComplex.mk ((m ^ j.unop) • (𝟙 ((coefficients).action i))) φ
    (by exact cmHarrisCoefficientDiagram_scalar_comp D U ρ p m hm f)

local notation "actionSequence" => cmHarrisCoefficientScalarActionSequence D U ρ p m hm f

/-- The reduction kernel is exactly the image of the coarse scalar power. -/
theorem cmHarrisCoefficientScalarActionSequence_exact : (actionSequence).Exact := by
  apply ((actionSequence).exact_map_iff_of_faithful
    (Action.forget (ModuleCat.{0} Rcoeff) _)).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Submodule.Quotient.mk y : ((coefficients).action j).V) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨z, hz⟩ := (mem_principalPower_smul_top (m : Rcoeff) j.unop y).mp hx
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  change Submodule.Quotient.mk ((m ^ j.unop) • z) = Submodule.Quotient.mk y
  congr 1
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hz

/-- The original sheaf transition kills the same natural scalar power. -/
@[reassoc] theorem cmHarrisCoefficientSystem_scalar_comp :
    ((m ^ j.unop) • (𝟙 ((system).obj i))) ≫ (system).map f = 0 := by
  change ((m ^ j.unop) • (𝟙 ((Fassoc).obj ((coefficients).action i)))) ≫
    ((Fassoc).map φ ≫ (etaleAssociatedComparisonIso X covers coverProperty f).inv.app
      coefficients) = 0
  rw [← (Fassoc).map_id, ← (Fassoc).map_nsmul, ← Category.assoc,
    ← Functor.map_comp, cmHarrisCoefficientDiagram_scalar_comp, Functor.map_zero, zero_comp]

/-- The scalar sequence retains the actual varying-cover sheaf transition. -/
def cmHarrisCoefficientScalarSequence : ShortComplex (Sheaf J (ModuleCat.{0} Rcoeff)) :=
  ShortComplex.mk ((m ^ j.unop) • (𝟙 ((system).obj i))) ((system).map f)
    (cmHarrisCoefficientSystem_scalar_comp D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f)

local notation "scalarSequence" => cmHarrisCoefficientScalarSequence D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid f

/-- Additivity and the proved original-cover comparison identify both actual arrows. -/
def cmHarrisCoefficientScalarSequenceIso :
    (actionSequence).map Fassoc ≅ scalarSequence :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((etaleAssociatedComparisonIso X covers coverProperty f).app coefficients).symm
    (by simp [cmHarrisCoefficientScalarActionSequence, cmHarrisCoefficientScalarSequence])
    (Category.id_comp _)

/-- Exactness on the actual full-lattice reductions descends to the original sheaves. -/
theorem cmHarrisCoefficientScalarSequence_exact : (scalarSequence).Exact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := Rcoeff) X ((covers).action i)
    (coverProperty i)
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := Rcoeff) X ((covers).action i)
    (coverProperty i)
  exact ShortComplex.exact_of_iso
    (cmHarrisCoefficientScalarSequenceIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f)
    ((cmHarrisCoefficientScalarActionSequence_exact D U ρ p m hm f).map Fassoc)

/-- The actual transition is the cokernel of the coarse scalar power on the fine sheaf. -/
def cmHarrisCoefficientSystemScalarIsCokernel :
    IsColimit (CokernelCofork.ofπ ((system).map f)
      (cmHarrisCoefficientSystem_scalar_comp D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f)) := by
  letI : Epi (scalarSequence).g := cmHarrisCoefficientSystem_map_epi D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f
  exact (cmHarrisCoefficientScalarSequence_exact D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f).gIsCokernel

/-- Canonical scalar cokernel model of the actual original coarse coefficient sheaf. -/
def cmHarrisCoefficientSystemScalarCokernelIso :
    cokernel ((m ^ j.unop) • (𝟙 ((system).obj i))) ≅ (system).obj j :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (cmHarrisCoefficientSystemScalarIsCokernel D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f)

/-- The cokernel projection recovers the original transition exactly. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientSystemScalarCokernelIso_π_hom :
    cokernel.π ((m ^ j.unop) • (𝟙 ((system).obj i))) ≫
      (cmHarrisCoefficientSystemScalarCokernelIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid f).hom = (system).map f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
