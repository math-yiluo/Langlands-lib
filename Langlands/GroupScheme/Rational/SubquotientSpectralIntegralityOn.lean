import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality

/-! # Pointwise integral characteristic coefficients of actual subquotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [ValuativeRel k]
  {G : GroupScheme (Spec (CommRingCat.of k))} {a b : ℕ}
  {σ : MatrixRepresentation G (Fin a)} {ρ : MatrixRepresentation G (Fin b)}

/-- At each actual rational point, integral characteristic coefficients pass
from a representation to any actual representation subquotient. -/
theorem IsSubquotientOf.charpoly_coeff_vle_one
    (h : IsSubquotientOf σ ρ) (g : rationalPoints G)
    (hρ : ∀ i, (ρ.rationalMatrix g : Matrix (Fin b) (Fin b) k).charpoly.coeff i
      ≤ᵥ (1 : k)) :
    ∀ i, (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly.coeff i
      ≤ᵥ (1 : k) := by
  obtain ⟨r, τ, C, D, hC, hi, hD, hs⟩ := h
  exact Langlands.charpoly_coeff_vle_one_of_surjective_intertwiner D hs
    (hD.rationalMatrix g)
    (Langlands.charpoly_coeff_vle_one_of_injective_intertwiner C hi
      (hC.rationalMatrix g) hρ)

/-- The pointwise inheritance theorem applies to any subset of actual points,
including an image under scalar extension. -/
theorem IsSubquotientOf.charpoly_coeff_vle_one_on
    (h : IsSubquotientOf σ ρ) (S : Set (rationalPoints G))
    (hρ : ∀ g ∈ S, ∀ i,
      (ρ.rationalMatrix g : Matrix (Fin b) (Fin b) k).charpoly.coeff i ≤ᵥ (1 : k)) :
    ∀ g ∈ S, ∀ i,
      (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly.coeff i ≤ᵥ (1 : k) :=
  fun g hg => h.charpoly_coeff_vle_one g (hρ g hg)

/-- A monic valuation-ring lift of the actual subquotient characteristic
polynomial, using integral coefficients only at the given point. -/
def integralCharpolyOfSubquotientAt (h : IsSubquotientOf σ ρ) (g : rationalPoints G)
    (hρ : ∀ i, (ρ.rationalMatrix g : Matrix (Fin b) (Fin b) k).charpoly.coeff i
      ≤ᵥ (1 : k)) :
    {p : Polynomial (ValuativeRel.valuation k).integer //
      p.Monic ∧
      p.map (algebraMap (ValuativeRel.valuation k).integer k) =
        (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly ∧
      p.natDegree = a} := by
  classical
  apply Classical.choice
  have hl : (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly ∈
      Polynomial.lifts (algebraMap (ValuativeRel.valuation k).integer k) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, (ValuativeRel.valuation k).vle_iff_le.mp
      (h.charpoly_coeff_vle_one g hρ i)⟩, rfl⟩
  obtain ⟨p, hmap, hdeg, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (σ.rationalMatrix g : Matrix (Fin a) (Fin a) k).charpoly_monic
  exact ⟨⟨p, hmonic, hmap, by simpa using hdeg⟩⟩

end Langlands.GroupScheme.MatrixRepresentation
