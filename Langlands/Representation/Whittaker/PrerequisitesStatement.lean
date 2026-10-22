import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Whittaker uniqueness and model prerequisites

Concrete functional formulation for the actual matrix general linear group.
JPSS (1983), Sections 0.3 and 2.1-2.2, printed pages 375-378 and 385-386.
This is a proposition target, not an assertion that its clauses are proved.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- Multiplicity one, inversion of the additive character, and injectivity of
the Whittaker orbit-function map, for every positive rank and p-adic field.

The local `equivariant` predicate spells out the actual upper-unitriangular
matrix equations and the standard nondegenerate character. It does not
parameterize the statement by an arbitrary predicate or a desired theorem. -/
def WhittakerPrerequisitesStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      let equivariant := fun (χ : AddChar F.Carrier ℂ) (ℓ : Module.Dual ℂ V) =>
        ∀ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier,
          (∀ i j, j < i → g.val i j = 0) →
          (∀ i, g.val i i = 1) →
          ∀ v, ℓ (ρ g v) = (∏ i : Fin n, χ (g.val i.castSucc i.succ)) * ℓ v
      (∀ ℓ₁ ℓ₂ : Module.Dual ℂ V,
        equivariant ψ ℓ₁ → equivariant ψ ℓ₂ → ℓ₁ ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁) ∧
      ((∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ψ ℓ) ↔
        ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ψ⁻¹ ℓ) ∧
      (∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 → equivariant ψ ℓ →
        Function.Injective (fun v => fun g => ℓ (ρ g v)))

end Langlands
