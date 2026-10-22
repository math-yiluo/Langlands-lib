import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Existence, uniqueness and minimality of the newvector level

This is a proposition target, with no proof asserted. It extracts the
fixed-vector content of JPSS, Conducteur (1981), Section 5.1, using the
essential-vector existence correction of Jacquet (2012), Theorem 1.
The equality with the epsilon-factor exponent is a separate target.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- A generic irreducible admissible representation has a minimal newvector
level, and the fixed-vector space at that level is a line. The congruence
conditions use the actual valuation ring and powers of its maximal ideal. -/
def NewvectorStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧
        ∀ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier,
          (∀ i j, j < i → g.val i j = 0) →
          (∀ i, g.val i i = 1) →
          ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      let level := fun (a : ℕ)
          (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) =>
        (∀ i j, g.val i j ∈ T.Integers) ∧
        (∀ i j, (g⁻¹).val i j ∈ T.Integers) ∧
        ∀ j : Fin (n + 1),
          ∃ x : T.Integers, x ∈ (IsLocalRing.maximalIdeal T.Integers) ^ a ∧
            (x : F.Carrier) = g.val (Fin.last n) j - if j = Fin.last n then 1 else 0
      let fixed := fun a v => ∀ g, level a g → ρ g v = v
      ∃ (m : ℕ) (v : V), v ≠ 0 ∧ fixed m v ∧
        (∀ w : V, fixed m w → ∃! c : ℂ, w = c • v) ∧
        (∀ (a : ℕ) (w : V), w ≠ 0 → fixed a w → m ≤ a)

end Langlands
