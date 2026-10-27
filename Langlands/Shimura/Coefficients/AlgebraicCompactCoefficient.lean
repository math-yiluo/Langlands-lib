import Langlands.Shimura.Coefficients.AlgebraicOrbitContinuityProof
import Langlands.Shimura.NormalLevelContinuous

/-! # Compact algebraic coefficients with continuity derived from naturality -/

noncomputable section

universe u v w

namespace Langlands.Shimura.Coefficients

open Langlands.Global CategoryTheory Opposite
open scoped TensorProduct

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (l : FinitePlace L)

local instance : TopologicalSpace (FiniteCompletion L l ⊗[L] W) := coefficientTopology L l W

/-- Naturality of the actual algebraic representation gives continuous local orbit maps. -/
theorem continuous_algebraicCoefficient_orbit (x : FiniteCompletion L l ⊗[L] W) :
    Continuous (fun g : (σ.baseChange L).Points (FiniteCompletion L l) =>
      ρ.act (FiniteCompletion L l) g x) :=
  ρ.continuous_act x

variable [l.asIdeal.LiesOver p.asIdeal]

/-- The actual finite-adelic coefficient action has continuous orbit maps. -/
theorem continuous_algebraicAdelicCoefficient_orbit (x : FiniteCompletion L l ⊗[L] W) :
    Continuous (fun g : σ.FiniteAdelicPoints => ρ.placeAction p l g x) :=
  ρ.continuous_placeAction_orbit p l (continuous_algebraicCoefficient_orbit ρ l) x

variable [Module.Finite L W] (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- The compact-level stable lattice, with its continuity prerequisite proved from naturality. -/
def algebraicCompactCoefficientLattice : StableCoefficientLattice ρ p l U.subgroup :=
  compactStableCoefficientLattice ρ p l U (continuous_algebraicCoefficient_orbit ρ l)

/-- Its carrier remains the actual orbit span of the coordinate lattice. -/
@[simp] theorem algebraicCompactCoefficientLattice_carrier :
    (algebraicCompactCoefficientLattice ρ p l U).carrier = compactCoefficientLattice ρ p l U :=
  rfl

/-- The constructed lattice is open for the completion-module topology. -/
theorem algebraicCompactCoefficientLattice_isOpen :
    IsOpen ((algebraicCompactCoefficientLattice ρ p l U).carrier :
      Set (FiniteCompletion L l ⊗[L] W)) :=
  (compactCoefficientLattice_properties ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l)).2.2

/-- The integral action has continuous orbit maps in the actual lattice subtype topology. -/
theorem continuous_algebraicCompactCoefficientAction_orbit
    (x : (algebraicCompactCoefficientLattice ρ p l U).action.V) :
    Continuous (fun g : U.subgroup =>
      ((algebraicCompactCoefficientLattice ρ p l U).action.ρ g).hom x) :=
  continuous_compactCoefficientAction_orbit ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) x

/-- Every nonzero rational scalar power has an open action kernel and finite group quotient. -/
theorem algebraicCompactCoefficient_congruenceKernel (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    IsOpen (congruenceKernel (coefficientScalarIdeal l m)
      (algebraicCompactCoefficientLattice ρ p l U).action n : Set U.subgroup) ∧
    Finite ((algebraicCompactCoefficientLattice ρ p l U).RationalCongruenceGroup m n) :=
  compactCoefficient_congruenceKernel ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) m hm n

/-- The actual quotient-ring coefficient representation of the actual congruence group. -/
def algebraicCompactFiniteCoefficientAction (m n : ℕ) :
    Action (ModuleCat.{u} (CoefficientReductionRing l m n))
      ((algebraicCompactCoefficientLattice ρ p l U).RationalCongruenceGroup m n) :=
  (algebraicCompactCoefficientLattice ρ p l U).rationalCongruenceAction m n

/-- Pullback along the quotient homomorphism recovers the constructed torsion action. -/
@[simp] theorem algebraicCompactFiniteCoefficientAction_mk (m n : ℕ) (g : U.subgroup) :
    (algebraicCompactFiniteCoefficientAction ρ p l U m n).ρ (QuotientGroup.mk g) =
      ((algebraicCompactCoefficientLattice ρ p l U).rationalTorsionAction l m n).ρ g :=
  rfl

/-- Nonzero scalar reductions have both a finite acting group and a finite coefficient module. -/
theorem algebraicCompactFiniteCoefficientAction_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite ((algebraicCompactCoefficientLattice ρ p l U).RationalCongruenceGroup m n) ∧
    Finite (algebraicCompactFiniteCoefficientAction ρ p l U m n).V :=
  ⟨(algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).2,
    (algebraicCompactCoefficientLattice ρ p l U).rationalCongruenceAction_finite m hm n⟩

/-- The integral-scalar coefficient diagram over these same varying congruence groups. -/
def algebraicCompactCoefficientDiagram (m : ℕ) :
    EquivariantDiagram
      ((algebraicCompactCoefficientLattice ρ p l U).rationalCongruenceGroups m)
      (ModuleCat.{u} (CoefficientIntegers l)) :=
  congruenceCoefficientDiagram (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action

/-- These are the original quotient-module reduction maps, and they are surjective. -/
theorem algebraicCompactCoefficientDiagram_transition_surjective (m : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    Function.Surjective ((algebraicCompactCoefficientDiagram ρ p l U m).transition f).hom :=
  congruenceCoefficientDiagram_transition_surjective (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action f

variable (m : ℕ) (hm : m ≠ 0)

/-- The actual compact-open ambient congruence levels, without an orbit-continuity input. -/
def algebraicCompactCongruenceLevels : ℕᵒᵖ ⥤ CompactOpenLevel σ.FiniteAdelicPoints :=
  compactCoefficientCongruenceLevels ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) m hm

variable {Γ : Type v} {X : Type w} [Group Γ] [MulAction Γ X] [TopologicalSpace X]
variable (ι : Γ →* σ.FiniteAdelicPoints)

/-- Actual double quotients with the same congruence groups that act on the coefficients. -/
def algebraicCompactCongruenceSpaces :
    EquivariantDiagram
      ((algebraicCompactCoefficientLattice ρ p l U).rationalCongruenceGroups m)
      TopCat.{max u w} :=
  compactCoefficientCongruenceSpaces (X := X) ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) m hm ι

@[simp] theorem algebraicCompactCongruenceSpaces_obj :
    (algebraicCompactCongruenceSpaces (X := X) ρ p l U m hm ι).obj =
      algebraicCompactCongruenceLevels ρ p l U m hm ⋙
        LevelSpace.tower (X := X) (ι := ι) :=
  rfl

/-- The natural forgetful projection to the original level. -/
def algebraicCompactCongruenceProjection :
    (algebraicCompactCongruenceSpaces (X := X) ρ p l U m hm ι).obj ⟶
      (Functor.const ℕᵒᵖ).obj (TopCat.of (LevelSpace (X := X) ι U.subgroup)) :=
  compactCoefficientCongruenceProjection (X := X) ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) m hm ι

/-- The constructed projection at every exponent is surjective. -/
theorem algebraicCompactCongruenceProjection_surjective (n : ℕᵒᵖ) :
    Function.Surjective
      ((algebraicCompactCongruenceProjection (X := X) ρ p l U m hm ι).app n) :=
  congruenceLevelProjection_surjective (X := X) U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun k => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm k).1) ι n

/-- The same actual spaces form an inverse diagram with jointly continuous fixed-level action. -/
def algebraicCompactContinuousLevelSpaces :
    ℕᵒᵖ ⥤ ContAction TopCat.{max u w} U.subgroup :=
  compactCoefficientContinuousLevelSpaces (X := X) ρ p l U
    (continuous_algebraicCoefficient_orbit ρ l) m hm ι

/-- Forgetting the continuous action recovers the actual equivariant quotient-space objects. -/
@[simp] theorem algebraicCompactContinuousLevelSpaces_obj (n : ℕᵒᵖ) :
    ((algebraicCompactContinuousLevelSpaces (X := X) ρ p l U m hm ι).obj n).obj.V =
      (algebraicCompactCongruenceSpaces (X := X) ρ p l U m hm ι).obj.obj n :=
  rfl

/-- The continuous transition maps retain the identity on double-quotient representatives. -/
@[simp] theorem algebraicCompactContinuousLevelSpaces_map_mk {i j : ℕᵒᵖ}
    (f : i ⟶ j) (x : X × σ.FiniteAdelicPoints) :
    ((algebraicCompactContinuousLevelSpaces (X := X) ρ p l U m hm ι).map f).hom.hom
        (LevelSpace.mk ((algebraicCompactCongruenceLevels ρ p l U m hm).obj i).subgroup x) =
      LevelSpace.mk ((algebraicCompactCongruenceLevels ρ p l U m hm).obj j).subgroup x :=
  congruenceContinuousLevelSpaces_map_mk (X := X) U (coefficientScalarIdeal l m)
    (algebraicCompactCoefficientLattice ρ p l U).action
    (fun k => (algebraicCompactCoefficient_congruenceKernel ρ p l U m hm k).1) ι f x

end Langlands.Shimura.Coefficients
