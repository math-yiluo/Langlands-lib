import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientScalar
import Langlands.Cohomology.DivisibleSystem
import Mathlib.Algebra.Module.Torsion.Field

/-! # Scalar flatness of original CM coefficient sheaves -/

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

local notation "ordinaryLevel" => CompactOpenLevel.inverseOpposite U.obj
local notation "lattice" => (harrisLatticeAction ρ p ordinaryLevel).V

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- A nonzero natural scalar acts injectively on the actual full Harris lattice. -/
theorem cmHarrisLattice_nsmul_injective (r : ℕ) (hr : r ≠ 0) :
    Function.Injective (fun x : lattice => r • x) := by
  have : IsAddTorsionFree ((K ⊗[ℚ] Global.FiniteCompletion ℚ p) ⊗[K] W) :=
    .of_isTorsionFree K _
  intro x y hxy
  apply Subtype.ext
  exact (nsmul_right_injective hr) (congrArg Subtype.val hxy)

/-- Every original coefficient action is killed by its defining scalar power. -/
theorem cmHarrisCoefficientDiagram_powSMul_eq_zero (k : ℕ) :
    powSMul m k ((coefficients).action (op k)) = 0 := by
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Submodule.Quotient.mk ((m ^ k) • y) :
    ((coefficients).action (op k)).V) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (mem_principalPower_smul_top (m : Rcoeff) k _).mpr
  exact ⟨y, by simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

/-- Complementary scalar powers on the actual full-lattice quotient action. -/
def cmHarrisCoefficientPowerActionSequence (a b : ℕ) :
    ShortComplex (Action (ModuleCat.{0} Rcoeff)
      ((cmHarrisCoefficientGroups D ρ p U m hm).obj (op (a + b)))) :=
  ShortComplex.mk (powSMul m a ((coefficients).action (op (a + b))))
    (powSMul m b ((coefficients).action (op (a + b))))
    (by rw [powSMul_comp_powSMul, cmHarrisCoefficientDiagram_powSMul_eq_zero])

/-- Scalar cancellation on the full lattice proves complementary-power exactness. -/
theorem cmHarrisCoefficientPowerActionSequence_exact (a b : ℕ) :
    (cmHarrisCoefficientPowerActionSequence D U ρ p m hm a b).Exact := by
  apply ((cmHarrisCoefficientPowerActionSequence D U ρ p m hm a b).exact_map_iff_of_faithful
    (Action.forget (ModuleCat.{0} Rcoeff) _)).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (Submodule.Quotient.mk ((m ^ b) • y) :
    ((coefficients).action (op (a + b))).V) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨z, hz⟩ := (mem_principalPower_smul_top (m : Rcoeff) (a + b) _).mp hx
  have hzNat : (m ^ (a + b)) • z = (m ^ b) • y := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hz
  rw [Nat.add_comm a b, pow_add, mul_smul] at hzNat
  have hcancel := cmHarrisLattice_nsmul_injective D U ρ p (m ^ b) (pow_ne_zero b hm) hzNat
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  change Submodule.Quotient.mk ((m ^ a) • z) = Submodule.Quotient.mk y
  rw [hcancel]

/-- Each original CM coefficient sheaf is killed by its defining scalar power. -/
theorem cmHarrisCoefficientSystem_powSMul_eq_zero (k : ℕ) :
    powSMul m k ((system).obj (op k)) = 0 := by
  change powSMul m k ((etaleAssociatedFunctor (R := Rcoeff) X
    ((covers).action (op k))).obj ((coefficients).action (op k))) = 0
  rw [← map_powSMul, cmHarrisCoefficientDiagram_powSMul_eq_zero, Functor.map_zero]

/-- Complementary scalar powers on the existing original coefficient sheaf. -/
def cmHarrisCoefficientPowerSequence (a b : ℕ) :
    ShortComplex (Sheaf J (ModuleCat.{0} Rcoeff)) :=
  ShortComplex.mk (powSMul m a ((system).obj (op (a + b))))
    (powSMul m b ((system).obj (op (a + b))))
    (by rw [powSMul_comp_powSMul, cmHarrisCoefficientSystem_powSMul_eq_zero])

/-- Exact torsor association retains both specified scalar endomorphisms. -/
def cmHarrisCoefficientPowerSequenceIso (a b : ℕ) :
    (cmHarrisCoefficientPowerActionSequence D U ρ p m hm a b).map
      (etaleAssociatedFunctor (R := Rcoeff) X ((covers).action (op (a + b)))) ≅
    cmHarrisCoefficientPowerSequence D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid a b :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp [cmHarrisCoefficientPowerActionSequence, cmHarrisCoefficientPowerSequence,
        map_powSMul])
    (by
      simp [cmHarrisCoefficientPowerActionSequence, cmHarrisCoefficientPowerSequence,
        map_powSMul])

/-- Complementary-power exactness holds in the original small-etale sheaf category. -/
theorem cmHarrisCoefficientPowerSequence_exact (a b : ℕ) :
    (cmHarrisCoefficientPowerSequence D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid a b).Exact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := Rcoeff) X
    ((covers).action (op (a + b))) (coverProperty (op (a + b)))
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := Rcoeff) X
    ((covers).action (op (a + b))) (coverProperty (op (a + b)))
  exact ShortComplex.exact_of_iso
    (cmHarrisCoefficientPowerSequenceIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid a b)
    ((cmHarrisCoefficientPowerActionSequence_exact D U ρ p m hm a b).map _)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
