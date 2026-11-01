import Langlands.AlgebraicGeometry.Modules.ClosedSupportDimension
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Integral ideals and exact-dimensional ample section cokernels -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

/-- Actual support dimensions of nonzero integral ideals and section cokernels,
with an exact-dimensional coherent cokernel supplied by ampleness. -/
def IntegralSupportDimensionStatement : Prop :=
  (∀ (X : Scheme.{u}) [IsIntegral X] (I : X.Modules)
    (ι : I ⟶ structureModule X), Mono ι → ¬ IsZero I →
      closedStalkSupport I = ⊤ ∧ supportDimension I = topologicalKrullDim X) ∧
  (∀ (X : Scheme.{u}) [IsIntegral X] (L : Picard.LineBundle X)
    (s : GlobalSections L.obj),
    (trivializationOpen L.obj s : Set X).Nonempty →
      supportDimension (cokernel (sectionHom L.obj s)) =
        topologicalKrullDim {x : X // x ∉ trivializationOpen L.obj s}) ∧
  (∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : Picard.LineBundle X), L.IsAmple → ∀ d : ℕ,
    topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
        (L.sectionOpen s : Set X).Nonempty ∧
        (cokernel (sectionHom _ s)).IsQuasicoherent ∧
        HasFiniteAffineSections (cokernel (sectionHom _ s)) ∧
        supportDimension (cokernel (sectionHom _ s)) = (d : WithBot ℕ∞))

end Langlands.AlgebraicGeometry.Modules
