import Langlands.Representation.Geometric.WeylDefinitions
import Mathlib.Basic.Real.Basic

/-!
# Ordered block parameters determined by permuted diagonal coordinates

An internal finite-order and counting statement, motivated by the final
chamber-rigidity step in Silberger's Proposition 6.1.
-/

namespace Langlands.Exponents

/-- A permutation matching repeated strictly decreasing block parameters
determines an ordered block matching preserving sizes and parameter values. -/
def BlockParameterPermutationRigidityStatement : Prop :=
  ∀ (n : ℕ) (B C : GeneralLinear.BlockShape n)
    (t : Fin B.length → ℝ) (s : Fin C.length → ℝ),
    StrictAnti t → StrictAnti s →
    (∃ w : Equiv.Perm (Fin n),
      ∀ a : Fin n,
        t (Geometric.blockIndex B a) =
          s (Geometric.blockIndex C (w a))) →
    ∃ b : Fin B.length ≃o Fin C.length,
      ∀ i : Fin B.length, B.size i = C.size (b i) ∧ t i = s (b i)

end Langlands.Exponents
