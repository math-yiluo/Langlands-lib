import Langlands.AllFieldBZ.Representation.Geometric.RefinementFunctors
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.AllFieldBZ.Representation.Parabolic.ComposedFunctors
import Langlands.Representation.Parabolic.RefinementTransitivityStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinementTransitivityStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinementTransitivityStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause
open Langlands.GeneralLinear
open Langlands.Geometric
open CategoryTheory
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Natural normalized induction transitivity, with evaluation and the
normalization-correct inverse prescribed on the actual function spaces. -/
def NormalizedRefinementInductionTransitivityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup B
  let inner := T.normalizedRefinedInductionFunctor.{uF, uV} B S
  let outer := T.normalizedParabolicInductionFunctor B
  let direct := T.normalizedComposedInductionFunctor.{uF, uV} B S
  ∃ E : (inner ⋙ outer) ≅ direct,
    (∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S))
      (f : (inner ⋙ outer).obj A) (g : GeneralLinear n F.Carrier),
      Induction.eval _ _ (SmoothRep.hom (E.hom.app A) f) g =
        Induction.eval _ _ (Induction.eval _ _ f g) 1) ∧
    (∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S))
      (f : direct.obj A) (g : GeneralLinear n F.Carrier) (m : B.Levi F.Carrier),
      Induction.eval _ _
          (Induction.eval _ _ (SmoothRep.hom (E.inv.app A) f) g) m =
        (T.leviHalfModulus B m : ℂ)⁻¹ •
          Induction.eval _ _ f (B.leviEmbedding F.Carrier m * g))

end Langlands.AllFieldBZ.Parabolic
