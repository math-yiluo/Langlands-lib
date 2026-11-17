import Langlands.Algebra.AffineSpaceFiniteEtalePicardStatement
import Langlands.Algebra.IntegerFiniteEtalePicard
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Finite étale affine-space classification and the Picard reduction -/

universe u v w

namespace Langlands.Algebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- In characteristic zero, a finite étale algebra over affine space is a finite product
of polynomial rings over finite extension fields, as an algebra over the original
polynomial ring. The empty product is allowed. -/
def AffineSpaceFiniteEtaleClassificationStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (A : Type u) [CommRing A]
    [Algebra (MvPolynomial (Fin n) k) A],
    Algebra.Etale (MvPolynomial (Fin n) k) A → Module.Finite (MvPolynomial (Fin n) k) A →
      ∃ (m : ℕ) (K : Fin m → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra k (K i)),
        (∀ i, Module.Finite k (K i)) ∧
          Nonempty (A ≃ₐ[MvPolynomial (Fin n) k] (∀ i, MvPolynomial (Fin n) (K i)))

/-- A finite product of rings with trivial Picard groups has trivial Picard group. -/
theorem subsingleton_pic_pi_of_finite {ι : Type w} [Finite ι] (B : ι → Type v)
    [∀ i, CommRing (B i)] [∀ i, Subsingleton (CommRing.Pic (B i))] :
    Subsingleton (CommRing.Pic (∀ i, B i)) := by
  let : ∀ i, Algebra (∀ j, B j) (B i) := fun i => (Pi.evalRingHom B i).toAlgebra
  apply subsingleton_pic_of_bijective_algebraMap_pi B
  change Function.Bijective (fun x : (∀ i, B i) => x)
  exact Function.bijective_id

/-- A finite product of polynomial rings over fields has trivial Picard group. -/
theorem subsingleton_pic_pi_mvPolynomial {ι : Type w} [Finite ι]
    (K : ι → Type v) [∀ i, Field (K i)] (n : ℕ) :
    Subsingleton (CommRing.Pic (∀ i, MvPolynomial (Fin n) (K i))) := by
  let : ∀ i, Subsingleton (CommRing.Pic (MvPolynomial (Fin n) (K i))) :=
    fun _ => inferInstance
  exact subsingleton_pic_pi_of_finite _

/-- The finite-product classification implies the unchanged affine-space Picard target. -/
theorem affineSpaceFiniteEtalePicardTrivialStatement_of_classification
    (h : AffineSpaceFiniteEtaleClassificationStatement.{u}) :
    AffineSpaceFiniteEtalePicardTrivialStatement.{u} := by
  intro k _ _ n A _ _ het hfin
  obtain ⟨m, K, hK, hAlg, _, ⟨e⟩⟩ := h k n A het hfin
  let := hK
  let := hAlg
  let := subsingleton_pic_pi_mvPolynomial K n
  exact subsingleton_pic_of_ringEquiv e.toRingEquiv

end Langlands.Algebra
