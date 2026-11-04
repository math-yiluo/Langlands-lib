import Langlands.GroupScheme.Rational.TorusVectorLinearizationStatement
import Langlands.GroupScheme.Rational.VectorActionCharZero
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Reduction of torus linearization to positive characteristic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Every torus action on a vector group is linear in suitable natural coordinates,
once natural coordinates that are scalar linear on coefficient tests are known in
every prime characteristic. Characteristic zero is the published scalar-linearity
theorem; the torus is affine, which upgrades coefficient tests to all scheme tests. -/
theorem torusVectorActionLinearization_of_charP
    (hp : ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (T V : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ),
      IsTorus T → IsVectorGroupOfDimension V n → ∀ a : AutomorphicAction T V,
      ∃ e : ∀ W : Over (Spec (CommRingCat.of k)),
          (W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤)),
        IsNaturalVectorCoordinates e ∧ IsAffineLinearVectorCoordinates a e) :
    TorusVectorActionLinearizationStatement.{u} := by
  intro k _ T V n hT hV a
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  obtain ⟨p, hchar⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨e, he, ha⟩ := hp k p T V n hT hV a
    exact ⟨e, ha.isLinearVectorCoordinates he⟩
  · have := CharP.charP_to_charZero k
    obtain ⟨e, he⟩ := hV
    exact ⟨e, isLinearVectorCoordinates_of_charZero he⟩

end Langlands.GroupScheme.RelativeRoot
