import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof

/-! # Characteristic-zero invariant separation for reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A reductive group in characteristic zero admits a degree-one invariant
polynomial taking value one at any prescribed nonzero fixed vector. -/
theorem exists_normalized_invariant_polynomial_of_reductive_charZero
    (ρ : MatrixRepresentation G n) (hG : IsPseudoReductive G)
    (v : n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ F : MvPolynomial n k, F.IsHomogeneous 1 ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
          (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F = 1 := by
  let := hG.smooth
  obtain ⟨c, hc, hcv⟩ := ρ.exists_dual_fixed_of_rational_semisimple
    (reductiveCharZeroSemisimplicityStatement k G hG n ρ) v hv hfix
  refine ⟨linearPolynomial c, linearPolynomial_isHomogeneous c,
    invariant_linearPolynomial_of_dual_fixed ρ c hc, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id k) v (linearPolynomial c) = 1
  simpa only [eval_linearPolynomial, RingHom.id_apply] using hcv

/-- A chosen normalized degree-one invariant separator in characteristic zero. -/
def charZeroInvariantPolynomial (ρ : MatrixRepresentation G n)
    (hG : IsPseudoReductive G) (v : n → k) (hv : v ≠ 0)
    (hfix : ρ.IsFixedVector v) : MvPolynomial n k :=
  Classical.choose
    (ρ.exists_normalized_invariant_polynomial_of_reductive_charZero hG v hv hfix)

/-- The chosen separator is homogeneous of degree one, invariant on every scheme
test, and normalized at the prescribed fixed vector. -/
theorem charZeroInvariantPolynomial_spec (ρ : MatrixRepresentation G n)
    (hG : IsPseudoReductive G) (v : n → k) (hv : v ≠ 0)
    (hfix : ρ.IsFixedVector v) :
    (ρ.charZeroInvariantPolynomial hG v hv hfix).IsHomogeneous 1 ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
          (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x)
            (ρ.charZeroInvariantPolynomial hG v hv hfix) =
          MvPolynomial.eval₂ (scalarMap T) x
            (ρ.charZeroInvariantPolynomial hG v hv hfix)) ∧
      MvPolynomial.eval v (ρ.charZeroInvariantPolynomial hG v hv hfix) = 1 :=
  Classical.choose_spec
    (ρ.exists_normalized_invariant_polynomial_of_reductive_charZero hG v hv hfix)

end MatrixRepresentation

/-- The polynomial conclusion of geometric reductivity holds unconditionally for
connected reductive groups over algebraically closed fields of characteristic zero. -/
theorem invariant_polynomial_of_reductive_charZero
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
      MvPolynomial.eval v F ≠ 0 :=
  invariant_polynomial_of_reductive_charZero_semisimplicity
    reductiveCharZeroSemisimplicityStatement G hG n ρ v hv hfix

end Langlands.GroupScheme
