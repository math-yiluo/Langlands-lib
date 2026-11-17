import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Detecting a p-adic polynomial by norms of resultants -/

namespace Langlands.LinearAlgebra

/-- Milne's polynomial norm-detection lemma, expressed using resultants rather
than roots in an algebraic closure. This is an unproved proposition. -/
def PadicPolynomialNormDetectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P Q : Polynomial ℚ_[p]),
    P.Monic → Q.Monic → P.natDegree = Q.natDegree →
      (∀ F : Polynomial ℤ,
        ‖Polynomial.resultant P (F.map (Int.castRingHom ℚ_[p]))‖ =
          ‖Polynomial.resultant Q (F.map (Int.castRingHom ℚ_[p]))‖) →
      P = Q

end Langlands.LinearAlgebra
