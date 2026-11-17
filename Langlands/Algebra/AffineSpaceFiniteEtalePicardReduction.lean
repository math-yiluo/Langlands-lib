import Langlands.Algebra.AffineSpaceFiniteEtaleDecompositionStatement
import Langlands.Algebra.AffineSpaceFiniteEtalePicardStatement
import Langlands.Algebra.IntegerFiniteEtalePicard
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Picard triviality from a polynomial product decomposition -/

universe u v w

namespace Langlands.Algebra

/-- A finite product of commutative rings with trivial Picard groups has trivial
Picard group. -/
theorem subsingleton_pic_pi {ι : Type w} [Finite ι] (R : ι → Type v)
    [∀ i, CommRing (R i)] [∀ i, Subsingleton (CommRing.Pic (R i))] :
    Subsingleton (CommRing.Pic (∀ i, R i)) := by
  let (i : ι) : Algebra (∀ j, R j) (R i) := (Pi.evalRingHom R i).toAlgebra
  apply subsingleton_pic_of_bijective_algebraMap_pi R
  change Function.Bijective (fun x : ∀ i, R i => x)
  exact Function.bijective_id

/-- A ring isomorphic to a finite product of polynomial rings over fields has
trivial Picard group. -/
theorem subsingleton_pic_of_polynomial_product {A : Type u} [CommRing A]
    {ι : Type w} [Finite ι] (K : ι → Type v) [∀ i, Field (K i)] (n : ℕ)
    (e : A ≃+* ∀ i, MvPolynomial (Fin n) (K i)) :
    Subsingleton (CommRing.Pic A) := by
  have : ∀ i, Subsingleton (CommRing.Pic (MvPolynomial (Fin n) (K i))) :=
    fun _ => inferInstance
  have := subsingleton_pic_pi (fun i => MvPolynomial (Fin n) (K i))
  exact subsingleton_pic_of_ringEquiv e

/-- The characteristic-zero polynomial product decomposition implies the exact
published Picard-triviality statement. -/
theorem affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct
    (h : AffineSpaceFiniteEtalePolynomialProductStatement.{u}) :
    AffineSpaceFiniteEtalePicardTrivialStatement.{u} := by
  intro k _ _ n A _ _ hét hfin
  obtain ⟨ι, hι, K, hK, ⟨e⟩⟩ := h k n A hét hfin
  let := hι
  let := hK
  exact subsingleton_pic_of_polynomial_product K n e

end Langlands.Algebra
