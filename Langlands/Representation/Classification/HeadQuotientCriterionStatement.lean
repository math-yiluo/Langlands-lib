import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Two irreducible quotients and a strong head

These proposition definitions state an internal algebraic criterion for an
irreducible head in the kernel-unique sense. Every representation carrier lies
in the same universe, independently of the universe of the group. The two
irreducible targets may be identical. No proof of the statements is supplied.
-/

namespace Langlands.Classification

universe uG uV

/-- Surjections onto irreducibles with unequal kernels jointly surject onto
the actual product representation. -/
def UnequalIrreducibleQuotientKernelsStatement : Prop :=
  ∀ (G : Type uG) [Group G] (V W₁ W₂ : Type uV)
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂]
    (ρ : Representation ℂ G V)
    (π₁ : Representation ℂ G W₁) (π₂ : Representation ℂ G W₂),
    Representation.IsIrreducible π₁ → Representation.IsIrreducible π₂ →
      ∀ (q₁ : ρ.IntertwiningMap π₁) (q₂ : ρ.IntertwiningMap π₂),
        Function.Surjective q₁ → Function.Surjective q₂ →
          LinearMap.ker q₁.toLinearMap ≠ LinearMap.ker q₂.toLinearMap →
            Function.Surjective (q₁.prod q₂)

/-- An irreducible head exists exactly when an irreducible quotient exists
and there is no quotient onto a product of two irreducibles, including two
copies of the same irreducible. All targets use the source carrier universe. -/
def IrreducibleHeadProductCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    HasIrreducibleHead ρ ↔
      (∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W)
        (π : Representation ℂ G W), IsIrreducibleQuotient ρ π) ∧
      (∀ (W₁ W₂ : Type uV)
        [AddCommGroup W₁] [Module ℂ W₁]
        [AddCommGroup W₂] [Module ℂ W₂]
        (π₁ : Representation ℂ G W₁) (π₂ : Representation ℂ G W₂),
        Representation.IsIrreducible π₁ → Representation.IsIrreducible π₂ →
          ∀ q : ρ.IntertwiningMap (π₁.prod π₂), ¬ Function.Surjective q)

/-- The two-irreducible-quotient criterion, packaged as a later proof target. -/
def HeadQuotientCriterionStatement : Prop :=
  UnequalIrreducibleQuotientKernelsStatement.{uG, uV} ∧
    IrreducibleHeadProductCriterionStatement.{uG, uV}

end Langlands.Classification
