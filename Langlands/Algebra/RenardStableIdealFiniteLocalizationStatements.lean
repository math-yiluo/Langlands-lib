import Langlands.Algebra.RenardCompatibleLocalizationNoetherianStatements
import Langlands.Algebra.RenardCompatibleStableImageStatements

/-!
# Actual localization under explicit stable-ideal finiteness

An internal form of the conclusions of Renard 2026, C.II, printed p. 279 /
PDF p. 285. The finiteness hypotheses below explicitly use complex-linear
stable subspaces. No source convention for a nonunital Noetherian algebra
is selected implicitly.
-/

set_option autoImplicit false

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Finite stable generation of every complex-linear left ideal, of the
source and of its actual localization implies stabilization and the
canonical compatible identification with every positive stable image. -/
def StableIdealFiniteLocalizationStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    (∀ P : Submodule ℂ B,
      (∀ b x : B, x ∈ P → b * x ∈ P) →
      ∃ S : Finset B, (↑S : Set B) ⊆ P ∧
        ∀ Q : Submodule ℂ B,
          (∀ b x : B, x ∈ Q → b * x ∈ Q) →
          (↑S : Set B) ⊆ Q → P ≤ Q) →
    (∃ S : Finset V, ∀ P : Submodule ℂ V,
      (∀ (b : B) (v : V), v ∈ P → ρ b v ∈ P) →
      (↑S : Set V) ⊆ P → P = ⊤) →
    (let a := f.toLinearMap
     let σ := localizedAction a ρ (fun b v => f.map_action' b v)
     ∃ S : Finset (Localized a), ∀ P : Submodule ℂ (Localized a),
       (∀ (b : B) (v : Localized a), v ∈ P → σ b v ∈ P) →
       (↑S : Set (Localized a)) ⊆ P → P = ⊤) →
    CompatibleLocalizationStabilizationAt ρ f ∧
      ∀ n : ℕ, 0 < n → Stable (f.toLinearMap ^ n) →
        CompatibleStablePowerImageAt ρ f n

end Langlands.Renard.AlgebraActionLocalization
