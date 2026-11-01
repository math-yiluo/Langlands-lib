import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.KrullDimension

/-! # Actual section exact sequences on integral schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Modules

/-- On an integral scheme a section which generates on a nonempty open
gives a short exact cokernel sequence. The cokernel vanishes exactly when
the section generates everywhere, and is supported outside its generation
open. An ample power on a proper positive-dimensional integral field
scheme admits such a section with nonzero cokernel. -/
def IntegralAmpleSectionCokernelStatement : Prop :=
  (∀ (X : Scheme.{u}) [IsIntegral X] (M : X.Modules)
    (s : GlobalSections M), (trivializationOpen M s : Set X).Nonempty →
      (ShortComplex.cokernelSequence (sectionHom M s)).ShortExact ∧
      (IsZero (cokernel (sectionHom M s)) ↔ trivializationOpen M s = ⊤) ∧
      stalkSupport (cokernel (sectionHom M s)) ⊆
        (trivializationOpen M s : Set X)ᶜ) ∧
  (∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → 0 < topologicalKrullDim X →
      ∀ (L : LineBundle X), L.IsAmple → ∀ x : X,
        ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
          x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s) ∧
          (ShortComplex.cokernelSequence
            (sectionHom (Langlands.Scheme.Modules.tensorPow L.obj n) s)).ShortExact ∧
          ¬ IsZero (cokernel
            (sectionHom (Langlands.Scheme.Modules.tensorPow L.obj n) s)) ∧
          stalkSupport (cokernel
            (sectionHom (Langlands.Scheme.Modules.tensorPow L.obj n) s)) ⊆
            (L.sectionOpen s : Set X)ᶜ)

end Langlands.AlgebraicGeometry.Picard
