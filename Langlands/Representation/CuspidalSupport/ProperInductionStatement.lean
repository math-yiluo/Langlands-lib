import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Subquotients

/-! BZ77 2.4(d): proper normalized induction has no quasicuspidal subquotients. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Every quasicuspidal smooth subquotient of an actual representation
normalizedly induced from a proper standard refinement is zero. -/
def ProperRefinedInductionTheorem : Prop :=
  letI := T.topology
  ∀ S : BlockRefinement B, refinedParabolic F.Carrier B S ≠ ⊤ →
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S),
      ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D ((T.normalizedRefinedInductionFunctor B S).obj A) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

/-- BZ77 2.4(d), expressed using 2.4(a), for all positive-rank product Levis
over actual finite p-adic extensions with complex coefficients. -/
def PadicProperRefinedInductionTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
      ProperRefinedInductionTheorem.{uF, uV} T B

end Langlands.CuspidalSupport
