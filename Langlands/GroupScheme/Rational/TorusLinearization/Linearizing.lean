import Langlands.GroupScheme.Rational.TorusLinearization.Generation
import Langlands.GroupScheme.Rational.TorusLinearization.Coordinates

/-! # Linearizing coordinates for a point action in prime characteristic -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

namespace PointAction

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}

/-- Every point action in characteristic `p` is linearized by mutually inverse additive
polynomials over the ground field. -/
theorem exists_linearizing [Finite I] (a : PointAction k K I n) (p : ℕ) [Fact p.Prime]
    [CharP k p] :
    ∃ Φ Q : Fin n → MvPolynomial (Fin n) k, (∀ i, IsAddPoly (Φ i)) ∧
      (∀ j, aeval Φ (Q j) = X j) ∧ (∀ i, aeval Q (Φ i) = X i) ∧
      ∀ (B : Type u) [CommRing B] [Algebra k B] (t : a.Pt B), ∃ b : Fin n → Fin n → B,
        ∀ i, a.pull t (Φ i) = ∑ j, b i j • MvPolynomial.map (algebraMap k B) (Φ j) := by
  classical
  have := Fintype.ofFinite I
  obtain ⟨W, hWA, hWs, hinj, hgen⟩ := a.exists_subspace p
  exact a.exists_linearizing_of_subspace p W hWA hWs hinj hgen

end PointAction

end Langlands.GroupScheme.TorusLinearization
