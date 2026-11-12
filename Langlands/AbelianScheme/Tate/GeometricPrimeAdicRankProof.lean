import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankStatement
import Langlands.AbelianScheme.Tate.GeometricTorsionRankProof
import Langlands.AbelianScheme.Tate.PrimeAdicFreeness
import Langlands.AbelianScheme.Tate.PrimeAdicCoordinates

/-! # Rank of the actual prime-adic Tate module at a geometric point -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate.PrimeAdic

/-- At an algebraically closed point, the integral prime-adic Tate module of an
abelian scheme of relative dimension `g` is free of rank `2 * g`, and the rational
Tate module has dimension `2 * g`, for a prime invertible on the base. -/
theorem geometricPrimeAdicRank : GeometricPrimeAdicRankStatement.{u} := by
  intro S A g hg p _ hp Ω _ _ s
  have hlevel : ∀ n : ℕ,
      Nonempty ((Fin (2 * g) → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)]
        GroupScheme.Tate.Level A.toGrp (Over.mk s) (p ^ n)) ∧
      Nat.card (GroupScheme.Tate.Level A.toGrp (Over.mk s) (p ^ n)) = (p ^ n) ^ (2 * g) :=
    fun n => geometricTorsionRank S A g hg (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
      (by rw [Nat.cast_pow]; exact hp.pow n) Ω s
  obtain ⟨e⟩ := GroupScheme.Tate.PrimeAdic.integral_linearEquiv_of_level
    (fun n => (hlevel n).2) (fun n => (hlevel n).1)
  exact ⟨⟨e⟩, GroupScheme.Tate.PrimeAdic.rational_finrank_of_linearEquiv e⟩

end Langlands.AbelianScheme.Tate.PrimeAdic
