import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.KrullDimension

/-! # Base case and nonempty cuts for ample Euler positivity -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Finite closed support gives a positive Euler characteristic precisely for
a nonzero sheaf. In positive dimension a proper field scheme is not affine,
and ample sections with affine generation opens have nonempty complements. -/
def EulerPositivityPreparationStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)),
    (∀ (M : X.Modules) (hM : HasFiniteCohomology f M),
      HasFiniteClosedSupport M →
        eulerCharacteristic f M hM =
          (Module.finrank K ((relativeCohomology f 0).obj M) : ℤ) ∧
        (0 < eulerCharacteristic f M hM ↔ ¬ IsZero M)) ∧
    (IsProper f → 0 < topologicalKrullDim X →
      ¬ IsAffine X ∧
      ∀ (L : LineBundle X), L.IsAmple → ∀ x : X,
        ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
          x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s) ∧
          ∃ y : X, y ∉ L.sectionOpen s)

end Langlands.AlgebraicGeometry.Picard
