import Langlands.GroupScheme.Reductive.ConjugationDeterminant
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # The positive-characteristic endomorphism-map input to Haboush's theorem -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

/-- The simply connected semisimple positive-characteristic input: a nonzero fixed
vector maps to a nonzero scalar identity under an actual conjugation-equivariant
linear map. This is a proposition to be proved, not an assumed theorem. -/
def SimplyConnectedPositiveCharConjugationMapStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsSimplyConnected G →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) (v : n → k),
      v ≠ 0 → ρ.IsFixedVector v →
      ∃ (m : ℕ), 0 < m ∧
        ∃ (σ : MatrixRepresentation G (Fin m))
          (φ : MatrixRepresentation.ConjugationLinearMap ρ σ) (a : k),
          a ≠ 0 ∧ MatrixLinear.eval φ.coeff (RingHom.id k) v =
            a • (1 : Matrix (Fin m) (Fin m) k)

end Langlands.GroupScheme
