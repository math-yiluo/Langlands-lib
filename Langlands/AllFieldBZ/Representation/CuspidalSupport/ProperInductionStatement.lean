import Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors
import Langlands.Representation.CuspidalSupport.ProperInductionStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ProperInductionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ProperInductionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding PadicProperRefinedInductionTheorem ProperRefinedInductionTheorem
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable {F : LocalFieldPackage.{uF}}
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
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
      ProperRefinedInductionTheorem.{uF, uV} T B

end Langlands.AllFieldBZ.CuspidalSupport
