import Langlands.Representation.Archimedean.StandardQuotientFactorization

/-! # Strict dominance for the other constituents of a real standard module -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-- Repeat each real inducing exponent by the rank of its block. -/
def realLanglandsExponentList (ds : List RealBlock) : List ℝ :=
  ds.flatMap fun b => List.replicate b.rank (realBlockExponent b)

/-- In Langlands order, strict dominance means equal total sum, domination of
all partial sums, and strict inequality for at least one partial sum. -/
def RealLanglandsStrictlyBelow (es ds : List RealBlock) : Prop :=
  (realLanglandsExponentList es).sum = (realLanglandsExponentList ds).sum ∧
    (∀ k : ℕ, ((realLanglandsExponentList es).take k).sum ≤ ((realLanglandsExponentList ds).take k).sum) ∧
    ∃ k : ℕ, ((realLanglandsExponentList es).take k).sum < ((realLanglandsExponentList ds).take k).sum

local notation:max "Vstd" n:max ds:max =>
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- An irreducible admissible subquotient of a proper stable submodule of an
ordered standard module has strictly smaller Langlands exponent data. -/
def RealLanglandsConstituentDominanceStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n → realRank es = n →
    IsRealLanglandsOrdered ds → IsRealLanglandsOrdered es →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∀ (W : Submodule ℂ (Vstd n ds))
        (hW : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W),
        W ≠ ⊤ →
        ∀ q : W →ₗ[ℂ] V, IsGKSubquotientMap ρ π hW q →
          ∀ p : Vstd n es →ₗ[ℂ] V,
            p ≠ 0 → IsRealStandardIntertwiner n ρ π es p →
            RealLanglandsStrictlyBelow es ds

end Langlands.Archimedean
