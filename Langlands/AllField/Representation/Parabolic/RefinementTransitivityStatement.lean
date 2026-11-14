import Langlands.Representation.Parabolic.RefinementTransitivityStatement
import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.ComposedFunctors
/-! Normalized transitivity for the actual direct and iterated block functors. -/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause
open Langlands.AllField.Parabolic

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

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
    (∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S))
      (f : (inner ⋙ outer).obj A) (g : GeneralLinear n F),
      Induction.eval _ _ (SmoothRep.hom (E.hom.app A) f) g =
        Induction.eval _ _ (Induction.eval _ _ f g) 1) ∧
    (∀ (A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S))
      (f : direct.obj A) (g : GeneralLinear n F) (m : B.Levi F),
      Induction.eval _ _
          (Induction.eval _ _ (SmoothRep.hom (E.inv.app A) f) g) m =
        (T.leviHalfModulus B m : ℂ)⁻¹ •
          Induction.eval _ _ f (B.leviEmbedding F m * g))

end Langlands.AllField.Parabolic
