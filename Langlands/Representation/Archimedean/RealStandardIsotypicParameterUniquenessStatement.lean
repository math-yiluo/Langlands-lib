import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Representation.Archimedean.RealLargeStandardIrreducibleReduction

/-! # Real standard-module parameters in a common isotypic module -/

set_option autoImplicit false

open scoped TensorProduct

universe uV uW

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Two real standard modules of the same rank that embed in an isotypic module
of one irreducible admissible type have the same multiset of Mœglin data.
This is a consequence of Tadić (2009), Propositions 1.1 and 1.3, in the
Library's real standard-module model. -/
def RealStandardIsotypicParameterUniquenessStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) (W : Type uW)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W)
    (ξ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (ds es : List RealBlock)
    (A : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] W)
    (B : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) →ₗ[ℂ] W),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
    IsGKIsotypic ρ π σ ξ → realRank ds = n → realRank es = n →
    A ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds) σ ξ →
    Function.Injective A →
    B ∈ gkHoms (realStandardRep n es) (realStandardLie n es) σ ξ →
    Function.Injective B →
    (realMoeglinData ds).Perm (realMoeglinData es)

end Langlands.Archimedean
