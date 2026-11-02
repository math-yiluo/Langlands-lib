import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Serre vanishing for two ample line bundles on a proper scheme over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

/-- For a proper scheme over a field, a quasi-coherent module with finite affine
sections and two ample line bundles, one threshold `n₀` makes the actual cohomology
`Hⁱ(X, (M ⊗ L₁^a) ⊗ L₂^b)` zero for all `a, b ≥ n₀` and all `i > 0`. -/
def ProperAmplePairSerreVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f →
      ∀ (M : X.Modules), M.IsQuasicoherent →
        (∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) →
          ∀ (L₁ L₂ : LineBundle X), L₁.IsAmple → L₂.IsAmple →
            ∃ n₀ : ℕ, ∀ a b : ℕ, n₀ ≤ a → n₀ ≤ b → ∀ i : ℕ, 0 < i →
              IsZero ((DerivedSections.relativeCohomology f i).obj
                (Langlands.Scheme.Modules.tensorObj
                  (Langlands.Scheme.Modules.tensorObj M
                    (Langlands.Scheme.Modules.tensorPow L₁.obj a))
                  (Langlands.Scheme.Modules.tensorPow L₂.obj b)))

end Langlands.AlgebraicGeometry.Modules
