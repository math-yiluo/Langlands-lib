import Langlands.AlgebraicGeometry.Modules.CoherentGraphSupport
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Mathlib.AlgebraicGeometry.Properties

/-! # Nonzero ideal sheaves and smaller support quotients -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

/-- A nonzero ideal is the structure sheaf on some nonempty open of a
reduced scheme; on an integral scheme its quotient has smaller support. -/
def IntegralIdealOpenStatement : Prop :=
  (∀ (X : Scheme.{u}) [IsReduced X] (I : X.Modules)
    (ι : I ⟶ structureModule X), Mono ι → ¬ IsZero I →
      ∃ U : X.Opens, (U : Set X).Nonempty ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι)) ∧
  (∀ (X : Scheme.{u}) [IsIntegral X] (I : X.Modules)
    (ι : I ⟶ structureModule X), Mono ι → ¬ IsZero I →
      ∀ d : ℕ, topologicalKrullDim X ≤ d →
        HasSupportDimensionLT (cokernel ι) d)

end Langlands.AlgebraicGeometry.Modules
