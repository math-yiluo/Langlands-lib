import Langlands.Shimura.Coefficients.AlgebraicTopology
import Langlands.Shimura.Coefficients.LocalLattice
import Langlands.Shimura.Coefficients.PrincipalReduction
import Langlands.Shimura.Coefficients.LatticeTopologyProof
import Langlands.Shimura.Levels

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open Langlands.Global CategoryTheory
open scoped TensorProduct

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal]
variable (U : CompactOpenLevel σ.FiniteAdelicPoints)

local instance : TopologicalSpace (FiniteCompletion L l ⊗[L] W) := coefficientTopology L l W
local instance : IsTopologicalAddGroup (FiniteCompletion L l ⊗[L] W) :=
  IsModuleTopology.isTopologicalAddGroup (FiniteCompletion L l) _
local instance : CompactSpace U.subgroup := isCompact_iff_compactSpace.mp U.isCompact

namespace StableCoefficientLattice

variable {U' : Subgroup σ.FiniteAdelicPoints} (Λ : StableCoefficientLattice ρ p l U')

/-- The integral action uses the topology inherited from its actual lattice. -/
instance actionTopology : TopologicalSpace Λ.action.V :=
  inferInstanceAs (TopologicalSpace Λ.carrier)

instance actionTopologicalAddGroup : IsTopologicalAddGroup Λ.action.V :=
  inferInstanceAs (IsTopologicalAddGroup Λ.carrier)

instance actionModuleFinite : Module.Finite (CoefficientIntegers l) Λ.action.V :=
  inferInstanceAs (Module.Finite (CoefficientIntegers l) Λ.carrier)

end StableCoefficientLattice

/-- Orbit saturation of the actual coordinate lattice by the chosen adelic level. -/
def compactCoefficientLattice :
    Submodule (CoefficientIntegers l) (FiniteCompletion L l ⊗[L] W) :=
  orbitSpan ((ρ.placeAction p l).comp U.subgroup.subtype) (coefficientLattice L l W)

variable (hρ : ∀ x : FiniteCompletion L l ⊗[L] W,
  Continuous (fun g : (σ.baseChange L).Points (FiniteCompletion L l) =>
    ρ.act (FiniteCompletion L l) g x))

include hρ in
/-- Compactness and continuous algebraic orbit maps certify the explicit lattice. -/
theorem compactCoefficientLattice_properties :
    Submodule.IsLattice (FiniteCompletion L l) (compactCoefficientLattice ρ p l U) ∧
    IsStable ((ρ.placeAction p l).comp U.subgroup.subtype) (compactCoefficientLattice ρ p l U) ∧
    IsOpen (compactCoefficientLattice ρ p l U : Set (FiniteCompletion L l ⊗[L] W)) := by
  apply compactLattice (CoefficientIntegers l) (FiniteCompletion L l)
    (FiniteCompletion L l ⊗[L] W) U.subgroup
    ((ρ.placeAction p l).comp U.subgroup.subtype)
  · intro x
    exact (ρ.continuous_placeAction_orbit p l hρ x).comp continuous_subtype_val
  · exact coefficientLattice_isOpen L l W

/-- A stable coefficient lattice constructed from the level, not supplied as output data. -/
def compactStableCoefficientLattice : StableCoefficientLattice ρ p l U.subgroup where
  carrier := compactCoefficientLattice ρ p l U
  isLattice := (compactCoefficientLattice_properties ρ p l U hρ).1
  stable := orbitSpan_stable _ _

/-- The constructed integral action has continuous orbit maps in the inherited topology. -/
theorem continuous_compactCoefficientAction_orbit
    (x : (compactStableCoefficientLattice ρ p l U hρ).action.V) :
    Continuous (fun g : U.subgroup =>
      (((compactStableCoefficientLattice ρ p l U hρ).action).ρ g).hom x) := by
  apply Continuous.subtype_mk
  exact (ρ.continuous_placeAction_orbit p l hρ x.val).comp continuous_subtype_val

/-- Every nonzero rational scalar reduction has an open congruence kernel and finite quotient. -/
theorem compactCoefficient_congruenceKernel (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    IsOpen (congruenceKernel (coefficientScalarIdeal l m)
      (compactStableCoefficientLattice ρ p l U hρ).action n : Set U.subgroup) ∧
    Finite (U.subgroup ⧸ congruenceKernel (coefficientScalarIdeal l m)
      (compactStableCoefficientLattice ρ p l U hρ).action n) := by
  apply congruenceKernelTopology (CoefficientIntegers l) U.subgroup
    (compactStableCoefficientLattice ρ p l U hρ).action
    (continuous_compactCoefficientAction_orbit ρ p l U hρ)
    (coefficientScalarIdeal l m) n
  exact coefficientScalarPower_isOpen l W m hm
    (compactCoefficientLattice ρ p l U)
    (compactCoefficientLattice_properties ρ p l U hρ).2.2 n

/-- The torsion action factored through its actual congruence quotient. -/
def compactCoefficientQuotientAction (m n : ℕ) :
    Action (ModuleCat.{u} (CoefficientIntegers l))
      (U.subgroup ⧸ congruenceKernel (coefficientScalarIdeal l m)
        (compactStableCoefficientLattice ρ p l U hρ).action n) :=
  quotientTorsionAction (coefficientScalarIdeal l m)
    (compactStableCoefficientLattice ρ p l U hρ).action n _ le_rfl

/-- Pulling back along the quotient homomorphism recovers the original torsion action. -/
@[simp] theorem compactCoefficientQuotientAction_mk (m n : ℕ) (g : U.subgroup) :
    (compactCoefficientQuotientAction ρ p l U hρ m n).ρ (QuotientGroup.mk g) =
      (torsionAction (coefficientScalarIdeal l m)
        (compactStableCoefficientLattice ρ p l U hρ).action n).ρ g := rfl

end Langlands.Shimura.Coefficients
