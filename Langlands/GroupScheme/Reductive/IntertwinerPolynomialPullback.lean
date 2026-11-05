import Langlands.GroupScheme.Reductive.AffineFixedVectorRegular
import Langlands.GroupScheme.Reductive.InvariantPolynomialDescent
import Langlands.GroupScheme.Reductive.ConjugationDeterminant

/-! # Polynomial pullback along rectangular intertwiners -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

section RectangularPullback

variable {k : Type u} [CommRing k]
  {n m : Type} [Fintype n]

/-- Pull back a polynomial along a linear map whose coordinate types may differ. -/
def rectangularPullback (C : Matrix m n k) (F : MvPolynomial m k) :
    MvPolynomial n k :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j) F

/-- Evaluation of the pullback is evaluation at the scalar-extended linear image. -/
theorem eval₂_rectangularPullback (C : Matrix m n k) (F : MvPolynomial m k)
    {A : Type*} [CommRing A] (f : k →+* A) (x : n → A) :
    MvPolynomial.eval₂ f x (rectangularPullback C F) =
      MvPolynomial.eval₂ f (C.map f *ᵥ x) F := by
  rw [rectangularPullback, ← MvPolynomial.eval₂_assoc]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Rectangular linear substitution preserves each specified homogeneous degree. -/
theorem rectangularPullback_isHomogeneous (C : Matrix m n k)
    {F : MvPolynomial m k} {d : ℕ} (hF : F.IsHomogeneous d) :
    (rectangularPullback C F).IsHomogeneous d := by
  simpa only [rectangularPullback, Nat.one_mul] using hF.eval₂ (n := 1) MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j)
    (fun c => MvPolynomial.isHomogeneous_C _ c)
    (by
      intro i
      apply MvPolynomial.IsHomogeneous.sum
      intro j _
      exact MvPolynomial.isHomogeneous_C_mul_X (C i j) j)

/-- The pullback has the value of the original polynomial at the linear image. -/
theorem eval_rectangularPullback (C : Matrix m n k) (F : MvPolynomial m k)
    (v : n → k) :
    MvPolynomial.eval v (rectangularPullback C F) = MvPolynomial.eval (C *ᵥ v) F := by
  have hC : C.map (RingHom.id k) = C := rfl
  simpa only [MvPolynomial.eval₂_id, hC] using
    eval₂_rectangularPullback C F (RingHom.id k) v

end RectangularPullback

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}

/-- Pullback along an affine-test intertwiner preserves invariance on every scheme test. -/
theorem IsInvariantPolynomial.rectangularPullback {F : MvPolynomial m k}
    (hF : σ.IsInvariantPolynomial F) {C : Matrix m n k} (hC : Intertwines ρ σ C) :
    ρ.IsInvariantPolynomial (rectangularPullback C F) := by
  intro T g x
  rw [eval₂_rectangularPullback, eval₂_rectangularPullback, Matrix.mulVec_mulVec,
    hC.points T g, ← Matrix.mulVec_mulVec]
  exact hF T g _

/-- A supplied homogeneous separator pulls back with its degree and nonzero value. -/
theorem Intertwines.pullback_separator {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (v : n → k) {F : MvPolynomial m k} {d : ℕ} (hhom : F.IsHomogeneous d)
    (hinv : σ.IsInvariantPolynomial F) (hne : MvPolynomial.eval (C *ᵥ v) F ≠ 0) :
    (rectangularPullback C F).IsHomogeneous d ∧
      ρ.IsInvariantPolynomial (rectangularPullback C F) ∧
      MvPolynomial.eval v (rectangularPullback C F) ≠ 0 := by
  refine ⟨rectangularPullback_isHomogeneous C hhom, hinv.rectangularPullback hC, ?_⟩
  rwa [eval_rectangularPullback]

/-- An intertwiner sends all-test fixed vectors to all-test fixed vectors. -/
theorem Intertwines.isFixedVector {C : Matrix m n k} (hC : Intertwines ρ σ C)
    {v : n → k} (hv : ρ.IsFixedVector v) : σ.IsFixedVector (C *ᵥ v) := by
  intro T g
  have hmap :
      (fun i => scalarMap T ((C *ᵥ v) i)) =
        C.map (scalarMap T) *ᵥ (fun i => scalarMap T (v i)) := by
    funext i
    exact (scalarMap T).map_mulVec C v i
  rw [hmap, Matrix.mulVec_mulVec, ← hC.points T g, ← Matrix.mulVec_mulVec, hv T g]

end Langlands.GroupScheme.MatrixRepresentation
