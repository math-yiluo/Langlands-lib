import Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorIrreducibility
import Mathlib.FieldTheory.Perfect

/-! # Perfect-field transport of actual Frobenius coefficient fullness -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusAlgebra

open AdditiveDividedPowers AdditiveFrobeniusOperators AdditiveTensorAlgebra

variable {k : Type u} [Field k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Entrywise scalar-ring preimage of a matrix subalgebra. The scalar map need
not be a k-algebra homomorphism: it still sends scalar matrices to scalar matrices. -/
def scalarPreimage (f : k →+* k) (A : Subalgebra k (Matrix n n k)) :
    Subalgebra k (Matrix n n k) where
  carrier := {M | M.map f ∈ A}
  algebraMap_mem' c := by
    have h : (algebraMap k (Matrix n n k) c).map f =
        algebraMap k (Matrix n n k) (f c) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    change (algebraMap k (Matrix n n k) c).map f ∈ A
    rw [h]
    exact A.algebraMap_mem _
  add_mem' := by
    intro M N hM hN
    change f.mapMatrix (M + N) ∈ A
    rw [map_add]
    exact A.add_mem hM hN
  mul_mem' := by
    intro M N hM hN
    change (M * N).map f ∈ A
    rw [Matrix.map_mul]
    exact A.mul_mem hM hN

variable {I : Type v}
  (ρs : I → MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Every original coefficient-algebra element maps into the coefficient
algebra of the actual Frobenius-powered family, without a perfection premise. -/
theorem map_mem_coefficientAlgebra_frobeniusPower (e : ℕ)
    {M : Matrix n n k} (hM : M ∈ coefficientAlgebra ρs) :
    M.map (iterateFrobenius k p e) ∈
      coefficientAlgebra (fun i => (ρs i).frobeniusPower p e) := by
  have hle : coefficientAlgebra ρs ≤
      scalarPreimage (iterateFrobenius k p e)
        (coefficientAlgebra (fun i => (ρs i).frobeniusPower p e)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨i, d⟩, rfl⟩
    change (coefficientMatrix (ρs i) d).map (iterateFrobenius k p e) ∈
      coefficientAlgebra (fun i => (ρs i).frobeniusPower p e)
    rw [← coefficientMatrix_frobeniusPower_mul]
    exact coefficientMatrix_mem_coefficientAlgebra _ i (p ^ e * d)
  exact hle hM

/-- Over a perfect field, full original family coefficient algebra remains
full under the actual Frobenius operation, including entrywise coefficient Frobenius. -/
theorem coefficientAlgebra_frobeniusPower_eq_top [PerfectRing k p] (e : ℕ)
    (hfull : coefficientAlgebra ρs = ⊤) :
    coefficientAlgebra (fun i => (ρs i).frobeniusPower p e) = ⊤ := by
  apply top_unique
  intro M _
  obtain ⟨N, hN⟩ := (iterateFrobeniusEquiv k p e).mapMatrix.surjective M
  change N.map (iterateFrobenius k p e) = M at hN
  rw [← hN]
  apply map_mem_coefficientAlgebra_frobeniusPower
  rw [hfull]
  trivial

section Ambient

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
  (f : I → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))

/-- Perfect-field form of the actual tensor criterion: second-factor fullness
is required only before Frobenius. Low first-factor fullness remains explicit. -/
theorem isIrreducible_tensor_frobeniusPower_of_perfect
    [PerfectRing k p] [Nonempty n] [Nonempty m] (e : ℕ)
    (hfirst : truncatedCoefficientAlgebra (fun i => ρ.restrict (f i)) (p ^ e) = ⊤)
    (hsecond : coefficientAlgebra (fun i => σ.restrict (f i)) = ⊤) :
    (ρ.tensor (σ.frobeniusPower p e)).IsIrreducible := by
  apply AdditiveTensorIrreducibility.isIrreducible_tensor_frobeniusPower
    ρ f σ p e hfirst
  exact coefficientAlgebra_frobeniusPower_eq_top _ p e hsecond

end Ambient

end Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusAlgebra
