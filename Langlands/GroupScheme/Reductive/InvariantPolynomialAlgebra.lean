import Langlands.GroupScheme.Reductive.InvariantPolynomialUniversal
import Mathlib.RingTheory.Adjoin.FG

/-! # The graded subalgebra of invariant polynomials -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MatrixRepresentation

section PolynomialAlgebra

variable {A B : Type*} [CommRing A] [CommRing B] {n : Type}

/-- Homogeneous components commute with extension of coefficients. -/
theorem map_homogeneousComponent (f : A →+* B) (d : ℕ)
    (F : MvPolynomial n A) :
    MvPolynomial.map f (MvPolynomial.homogeneousComponent d F) =
      MvPolynomial.homogeneousComponent d (MvPolynomial.map f F) := by
  classical
  ext v
  by_cases h : v.degree = d <;>
    simp [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent, h]

variable [Fintype n]

/-- Homogeneous components commute with pullback by a linear map. -/
theorem linearPullback_homogeneousComponent (M : Matrix n n A) (d : ℕ)
    (F : MvPolynomial n A) :
    linearPullback M (MvPolynomial.homogeneousComponent d F) =
      MvPolynomial.homogeneousComponent d (linearPullback M F) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial v c =>
    have hv : (MvPolynomial.monomial v c).IsHomogeneous v.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hv,
      MvPolynomial.homogeneousComponent_of_mem (linearPullback_isHomogeneous M hv)]
    split_ifs <;> simp [linearPullback]
  | add F H hF hH =>
    simpa only [map_add, linearPullback, MvPolynomial.eval₂_add] using
      congrArg₂ (· + ·) hF hH

end PolynomialAlgebra

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The subalgebra of polynomials invariant on every test scheme. -/
def invariantPolynomialSubalgebra (ρ : MatrixRepresentation G n) :
    Subalgebra R (MvPolynomial n R) where
  carrier := ρ.IsInvariantPolynomial
  algebraMap_mem' c := by
    intro T g x
    simp [MvPolynomial.algebraMap_eq]
  add_mem' hF hH := by
    intro T g x
    simp only [MvPolynomial.eval₂_add, hF T g x, hH T g x]
  mul_mem' hF hH := by
    intro T g x
    simp only [MvPolynomial.eval₂_mul, hF T g x, hH T g x]

@[simp]
theorem mem_invariantPolynomialSubalgebra (ρ : MatrixRepresentation G n)
    (F : MvPolynomial n R) :
    F ∈ ρ.invariantPolynomialSubalgebra ↔ ρ.IsInvariantPolynomial F :=
  Iff.rfl

/-- The action polynomial commutes with each homogeneous component. -/
theorem actionPolynomial_homogeneousComponent (ρ : MatrixRepresentation G n)
    {T : Over (Spec R)} (g : T ⟶ G.X) (d : ℕ) (F : MvPolynomial n R) :
    ρ.actionPolynomial g (MvPolynomial.homogeneousComponent d F) =
      MvPolynomial.homogeneousComponent d (ρ.actionPolynomial g F) := by
  rw [actionPolynomial, map_homogeneousComponent, linearPullback_homogeneousComponent]
  rfl

/-- Homogeneous components of invariant polynomials of an affine group are
invariant on every test scheme, over any commutative coefficient ring. -/
theorem IsInvariantPolynomial.homogeneousComponent [IsAffine G.X.left]
    {ρ : MatrixRepresentation G n} {F : MvPolynomial n R}
    (hF : ρ.IsInvariantPolynomial F) (d : ℕ) :
    ρ.IsInvariantPolynomial (MvPolynomial.homogeneousComponent d F) := by
  apply ρ.isInvariantPolynomial_of_universal
  rw [actionPolynomial_homogeneousComponent, hF.actionPolynomial (𝟙 G.X),
    ← map_homogeneousComponent]

attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype n] [DecidableEq n] in
/-- The graded-ring projection of a polynomial is its homogeneous component. -/
theorem polynomial_proj_eq_homogeneousComponent (d : ℕ) (F : MvPolynomial n R) :
    GradedRing.proj (MvPolynomial.homogeneousSubmodule n R) d F =
      MvPolynomial.homogeneousComponent d F :=
  MvPolynomial.decomposition.decompose'_apply F d

/-- The invariant subalgebra of an affine group is closed under homogeneous
projections in the standard polynomial grading. -/
theorem invariantPolynomialSubalgebra_proj_mem (ρ : MatrixRepresentation G n)
    [IsAffine G.X.left] (d : ℕ) (F : MvPolynomial n R)
    (hF : F ∈ ρ.invariantPolynomialSubalgebra) :
    GradedRing.proj (MvPolynomial.homogeneousSubmodule n R) d F ∈
      ρ.invariantPolynomialSubalgebra := by
  rw [polynomial_proj_eq_homogeneousComponent]
  exact hF.homogeneousComponent d

/-- Finite generation of the invariant subalgebra is the explicit generator
condition used in the published Hilbert theorem statement. -/
theorem invariantPolynomialSubalgebra_fg_iff (ρ : MatrixRepresentation G n) :
    ρ.invariantPolynomialSubalgebra.FG ↔
      ∃ s : Finset (MvPolynomial n R),
        (∀ F ∈ s, ρ.IsInvariantPolynomial F) ∧
          ∀ F : MvPolynomial n R, ρ.IsInvariantPolynomial F →
            F ∈ Algebra.adjoin R (s : Set (MvPolynomial n R)) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_, ?_⟩
    · intro F hF
      change F ∈ ρ.invariantPolynomialSubalgebra
      rw [← hs]
      exact Algebra.subset_adjoin hF
    · intro F hF
      rw [hs]
      exact hF
  · rintro ⟨s, hs, hgen⟩
    exact ⟨s, le_antisymm (Algebra.adjoin_le hs) hgen⟩

end Langlands.GroupScheme.MatrixRepresentation
