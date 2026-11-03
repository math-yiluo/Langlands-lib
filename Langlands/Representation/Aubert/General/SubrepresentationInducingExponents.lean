import Langlands.Representation.Aubert.General.ProperSubrepresentationJacquet
import Langlands.Representation.Exponents.ScalarCentralExponents
import Langlands.Representation.Smooth.IrreducibleRealization

/-! # Inducing exponents of actual induction subrepresentations -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
  (σ : SmoothRep.{0, uG, uV} ℂ M)

/-- The Jacquet module of every nonzero invariant subspace of actual induction
is equivalent to the inducing object if both displayed modules are simple.
The underlying map is the actual first adjoint of the inclusion. -/
def subrepresentationJacquetInducingEquiv
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (hσ : σ.IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS : S ≠ ⊥) :
    ((jacquetFunctor.{uG, max uG uV} h hU).obj
      (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)).representation.Equiv
      σ.representation := by
  let A := (normalizedInductionFunctor h hU).obj σ
  let e := subrepresentationJacquetInclusionEquiv h hU hUc σ hJac S hS
  have hirr := SmoothRep.isIrreducible_of_equiv e.symm hJac
  have hi : hom (subtype A S) ≠ 0 := by
    intro he
    apply hS
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    exact congrArg (fun F : (subrepresentation A S).representation.IntertwiningMap
      A.representation => F ⟨v, hv⟩) he
  exact FirstAdjointness.equivalenceOfIrreducibleJacquet h hU
    (isUnimodularModulus_of_isLimitOfCompactSubgroups U hU hUc)
    (subrepresentation A S) σ hirr hσ (hom (subtype A S)) hi

@[simp]
theorem subrepresentationJacquetInducingEquiv_mk
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (hσ : σ.IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS : S ≠ ⊥) (v : S) :
    subrepresentationJacquetInducingEquiv h hU hUc σ hJac hσ S hS
      (Jacquet.Localization.mk
        (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S).representation
        U 1 v) =
      Induction.eval P (inducingRepresentation h hU σ) v.val 1 := rfl

include hUc in
/-- If the inducing object has the specified scalar full-center character,
that is the only possible full-center exponent of the actual inducing
Jacquet module of every nonzero subrepresentation. -/
theorem subrepresentation_jacquet_centralExponent_eq
    (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
    (hσ : σ.IsIrreducible)
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS : S ≠ ⊥)
    (χ₀ : Subgroup.center M →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center M) (v : σ),
      σ.representation (z : M) v = (χ₀ z : ℂ) • v)
    (χ : Subgroup.center M →* ℂˣ)
    (hχ : IsCentralExponent
      ((jacquetFunctor.{uG, max uG uV} h hU).obj
        (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)).representation χ) :
    χ = χ₀ := by
  let e := subrepresentationJacquetInducingEquiv h hU hUc σ hJac hσ S hS
  exact centralExponent_eq_of_scalar_injective e.toIntertwiningMap e.injective
    χ₀ hscalar χ hχ

end Langlands.Aubert.General
