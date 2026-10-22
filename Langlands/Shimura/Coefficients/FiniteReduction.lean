import Langlands.Shimura.Coefficients.PrincipalReduction
import Langlands.Global.CompletionResidueAdic
import Mathlib.RingTheory.LocalRing.Quotient

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open Langlands.Global CategoryTheory Opposite

variable {L : Type u} [Field L] [NumberField L] (l : FinitePlace L)

/-- Every nonzero ideal of the actual completed coefficient ring has finite quotient. -/
theorem coefficientQuotient_finite (I : Ideal (CoefficientIntegers l)) (hI : I ≠ ⊥) :
    Finite (CoefficientIntegers l ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (CoefficientIntegers l)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  infer_instance

/-- The coefficient ring reduced by a power of the ideal of a rational scalar. -/
abbrev CoefficientReductionRing (m n : ℕ) :=
  CoefficientIntegers l ⧸ coefficientScalarIdeal l m ^ n

/-- Rational-scalar reductions are finite, including at ramified coefficient places. -/
theorem coefficientReductionRing_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (CoefficientReductionRing l m n) := by
  let : CharZero (FiniteCompletion L l) :=
    Algebra.charZero_of_charZero L (FiniteCompletion L l)
  apply coefficientQuotient_finite
  rw [coefficientScalarIdeal, Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr hm)

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} {ρ : (σ.baseChange L).AlgebraicRepresentation W}
variable {p : FinitePlace ℚ} [l.asIdeal.LiesOver p.asIdeal]
variable {U : Subgroup σ.FiniteAdelicPoints}

namespace StableCoefficientLattice

variable (Λ : StableCoefficientLattice ρ p l U)

/-- The actual coefficient system reduced by successive powers of a rational scalar. -/
def rationalTorsionSystem (m : ℕ) :
    ℕᵒᵖ ⥤ Action (ModuleCat.{u} (CoefficientIntegers l)) U :=
  Λ.system (coefficientScalarIdeal l m)

/-- Each term of this system has a finite carrier for every nonzero rational scalar. -/
theorem rationalTorsionSystem_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite ((Λ.rationalTorsionSystem l m).obj (op n)).V := by
  let : Finite (CoefficientIntegers l ⧸ coefficientScalarIdeal l m ^ n) :=
    coefficientReductionRing_finite l m hm n
  let : Module.Finite (CoefficientIntegers l) Λ.action.V :=
    inferInstanceAs (Module.Finite (CoefficientIntegers l) Λ.carrier)
  exact torsionAction_finite (coefficientScalarIdeal l m) Λ.action n

/-- The transition maps between rational-scalar reductions are surjective. -/
theorem rationalTorsionSystem_transition_surjective (m : ℕ) {i j : ℕ} (h : i ≤ j) :
    Function.Surjective (((Λ.rationalTorsionSystem l m).map (homOfLE h).op).hom) :=
  torsion_transition_surjective (coefficientScalarIdeal l m) Λ.action h

/-- The same torsion action with scalars in the actual finite coefficient quotient ring. -/
def rationalTorsionAction (m n : ℕ) :
    Action (ModuleCat.{u} (CoefficientReductionRing l m n)) U :=
  ((Langlands.Coefficients.AdicSystem.reduction
    (coefficientScalarIdeal l m ^ n)).mapAction U).obj Λ.action

/-- The quotient-ring action is induced by the original integral action on representatives. -/
@[simp] theorem rationalTorsionAction_mk (m n : ℕ) (g : U) (x : Λ.action.V) :
    ((Λ.rationalTorsionAction l m n).ρ g).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((Λ.action.ρ g).hom x) := rfl

/-- The action over the quotient coefficient ring has the same finite torsion carrier. -/
theorem rationalTorsionAction_finite (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    Finite (Λ.rationalTorsionAction l m n).V :=
  Λ.rationalTorsionSystem_finite l m hm n

end StableCoefficientLattice

end Langlands.Shimura.Coefficients
