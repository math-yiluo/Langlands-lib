import Langlands.Representation.Parabolic.ComposedFunctors
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic

/-! Normalized transitivity for the actual direct and iterated block functors. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

/-- Natural normalized Jacquet transitivity sends the iterated class of a
vector to its class modulo the actual full composed radical. -/
def NormalizedRefinementJacquetTransitivityClause : Prop :=
  letI := T.topology
  ∃ E :
      (T.normalizedJacquetFunctor.{uF, uV} B ⋙
        T.normalizedRefinedJacquetFunctor B S) ≅
      T.normalizedComposedJacquetFunctor.{uF, uV} B S,
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (v : A),
      SmoothRep.hom (E.hom.app A)
        (refinedJacquetMk B S (T.normalizedJacquet B A.representation)
          (B.jacquetMk A.representation v)) =
        composedJacquetMk B S A.representation v

/-- The two actual normalized transitivity isomorphisms for every smooth
representation in an arbitrary carrier universe. -/
def NormalizedRefinementTransitivityStatement : Prop :=
  NormalizedRefinementInductionTransitivityClause.{uF, uV} F T B S ∧
  NormalizedRefinementJacquetTransitivityClause.{uF, uV} F T B S

end Langlands.Parabolic
