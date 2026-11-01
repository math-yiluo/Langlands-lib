import Langlands.Representation.IntegerLattice.GeneralizedWeightPolynomial

/-! # Evaluation of the particular block polynomials and compatible coefficient assembly -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- The particular scalar-polynomial matrix evaluates to the matrix of the
actual restricted lattice action after its coordinate character is restored. -/
def CommutingTupleGeneralizedWeightPolynomialActionStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ)
    (b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
      ℂ (generalizedWeightBlock A c)) (n : Lattice d)
    (p q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
    b.repr (generalizedWeightBlockRepresentation A c n (b q)) p =
      (coordinateCharacter c n : ℂ) *
        MvPolynomial.eval (fun t => (n.toAdd t : ℂ))
          (generalizedWeightPolynomialMatrix A c b p q)

/-- Every supplied compatible local/ambient basis pair yields the actual
coefficient expansion using one exact block support before all coefficients. -/
def CommutingTupleGeneralizedWeightPolynomialCoefficientStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V)
    (b : ∀ c : Fin d → ℂˣ,
      Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
        ℂ (generalizedWeightBlock A c))
    (B : Module.Basis
      (Σ c : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A c))) ℂ V),
    (∀ (c : Fin d → ℂˣ) (q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
      B ⟨c, q⟩ = (b c q : V)) →
    ∃ s : Finset (Fin d → ℂˣ),
      (∀ c : Fin d → ℂˣ, c ∈ s ↔ generalizedWeightBlock A c ≠ ⊥) ∧
      ∀ (v : V) (ell : V →ₗ[ℂ] ℂ) (n : Lattice d),
        ell (tupleRepresentationEquiv d V A n v) =
          ∑ c ∈ s, (coordinateCharacter c n : ℂ) *
            MvPolynomial.eval (fun t => (n.toAdd t : ℂ))
              (generalizedWeightCoefficientPolynomial A c (b c) B v ell)

/-- Actual compatible bases and exact finite block support can be chosen once
before every vector, algebraic functional and integer lattice point. -/
def CommutingTupleGeneralizedWeightPolynomialAssemblyStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V),
    ∃ (b : ∀ c : Fin d → ℂˣ,
        Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
          ℂ (generalizedWeightBlock A c))
      (B : Module.Basis
        (Σ c : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A c))) ℂ V)
      (s : Finset (Fin d → ℂˣ)),
      (∀ (c : Fin d → ℂˣ) (q : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        B ⟨c, q⟩ = (b c q : V)) ∧
      (∀ c : Fin d → ℂˣ, c ∈ s ↔ generalizedWeightBlock A c ≠ ⊥) ∧
      ∀ (v : V) (ell : V →ₗ[ℂ] ℂ) (n : Lattice d),
        ell (tupleRepresentationEquiv d V A n v) =
          ∑ c ∈ s, (coordinateCharacter c n : ℂ) *
            MvPolynomial.eval (fun t => (n.toAdd t : ℂ))
              (generalizedWeightCoefficientPolynomial A c (b c) B v ell)

/-- The closed conjunction of the particular block-action evaluation,
compatible-basis identity, and actual simultaneous choice of all witnesses. -/
def RenardCIIIPolynomialComparisonStatement : Prop :=
  CommutingTupleGeneralizedWeightPolynomialActionStatement.{u} ∧
    CommutingTupleGeneralizedWeightPolynomialCoefficientStatement.{u} ∧
    CommutingTupleGeneralizedWeightPolynomialAssemblyStatement.{u}

end Langlands
