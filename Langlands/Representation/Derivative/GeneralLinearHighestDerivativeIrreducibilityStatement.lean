import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of the highest actual general-linear derivative

The first assertion of Zelevinsky 1980, Theorem 8.1, stated for every
highest-order datum of the Library's actual derivative. No proof is given here.
-/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- The highest positive actual Bernstein-Zelevinsky derivative of an
irreducible smooth representation of `GL_N`, `N > 0`, is irreducible. -/
def GeneralLinearHighestDerivativeIrreducibility : Prop :=
  letI := T.topology
  ∀ (N : ℕ), 0 < N →
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      Representation.IsIrreducible π.representation →
        ∀ hd : GeneralLinearHighestDerivativeOrderData T ψ π,
          Representation.IsIrreducible
            ((generalLinearDerivative T ψ N hd.order hd.le_rank).obj π).representation

end Langlands.Derivative
