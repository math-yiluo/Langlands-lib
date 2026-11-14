import Langlands.Representation.CuspidalSupport.ProperInductionStatement
import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement
/-! BZ77 2.4(d): proper normalized induction has no quasicuspidal subquotients. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)

/-- Every quasicuspidal smooth subquotient of an actual representation
normalizedly induced from a proper standard refinement is zero. -/
def ProperRefinedInductionTheorem : Prop :=
  letI := T.topology
  ∀ S : BlockRefinement B, refinedParabolic F B S ≠ ⊤ →
    ∀ A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S),
      ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F),
        SmoothRep.IsSubquotient D ((T.normalizedRefinedInductionFunctor B S).obj A) →
        IsLeviQuasicuspidal B D.representation → Subsingleton D

/-- BZ77 2.4(d), expressed using 2.4(a), for all positive-rank product Levis
over actual finite p-adic extensions with complex coefficients. -/
def PadicProperRefinedInductionTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ), 0 < n → ∀ B : BlockShape n,
      ProperRefinedInductionTheorem.{uF, uV} T B

end Langlands.AllField.CuspidalSupport
