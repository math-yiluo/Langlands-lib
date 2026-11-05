import Langlands.GroupScheme.Reductive.InvariantLinearForm

/-! # Complete reducibility for reductive groups in characteristic zero -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field of characteristic zero, every finite
coordinate representation of a connected reductive group has semisimple actual
rational-point representation. This is the complete-reducibility prerequisite,
not an assumption discharged by the degree-one separation construction. -/
def ReductiveCharZeroSemisimplicityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
      (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
      ρ.rationalRepresentation.IsSemisimpleRepresentation

/-- Conditional application of characteristic-zero complete reducibility to
produce the all-test-scheme invariant required by geometric reductivity. -/
theorem invariant_polynomial_of_reductive_charZero_semisimplicity
    (hss : ReductiveCharZeroSemisimplicityStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsPseudoReductive G)
    (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (v : n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
          (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F ≠ 0 := by
  let := hG.smooth
  obtain ⟨F, hdeg, hinv, hval⟩ :=
    ρ.exists_invariant_polynomial_of_rational_semisimple
      (hss k G hG n ρ) v hv hfix
  exact ⟨1, F, Nat.zero_lt_one, hdeg, hinv, hval⟩

end Langlands.GroupScheme
