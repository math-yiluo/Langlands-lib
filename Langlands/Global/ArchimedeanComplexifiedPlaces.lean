import Langlands.Global.ArchimedeanLieAlgebra
import Langlands.Shimura.Unitary.ComplexMatrixSplitting

/-! # Complex matrix coordinates for the full archimedean Lie algebra -/

noncomputable section
universe u

open scoped Classical TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open NumberField
open Langlands.Shimura

variable (F : Type u) [Field F] [NumberField F]

local notation "RealPlaces" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "ComplexPlaces" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

/-- A real place gives one complex factor, and a complex place gives two
factors indexed by its two complex embeddings. -/
abbrev ComplexifiedPlace := RealPlaces ⊕ (ComplexPlaces × Bool)

private def flattenPlaceFactors :
    ((RealPlaces → ℂ) × (ComplexPlaces → ℂ × ℂ)) ≃ₐ[ℂ] (ComplexifiedPlace F → ℂ) where
  toFun p
    | .inl v => p.1 v
    | .inr (v, true) => (p.2 v).1
    | .inr (v, false) => (p.2 v).2
  invFun f := (fun v => f (.inl v), fun v => (f (.inr (v, true)), f (.inr (v, false))))
  left_inv p := by
    rcases p with ⟨p, q⟩
    rfl
  right_inv f := by
    funext v
    rcases v with v | ⟨v, b⟩
    · rfl
    · cases b <;> rfl
  map_mul' p q := by
    funext v
    rcases v with v | ⟨v, b⟩
    · rfl
    · cases b <;> rfl
  map_add' p q := by
    funext v
    rcases v with v | ⟨v, b⟩
    · rfl
    · cases b <;> rfl
  commutes' c := by
    funext v
    rcases v with v | ⟨v, b⟩
    · rfl
    · cases b <;> rfl

/-- Scalar extension of the mixed archimedean coefficient ring to `ℂ`,
with a separate coordinate for each complexified place. -/
def complexifiedScalarCoordinates :
    (ℂ ⊗[ℝ] mixedEmbedding.mixedSpace F) ≃ₐ[ℂ] (ComplexifiedPlace F → ℂ) :=
  (Algebra.TensorProduct.prodRight ℝ ℂ ℂ (RealPlaces → ℝ) (ComplexPlaces → ℂ)).trans
    (((Algebra.TensorProduct.piScalarRight ℝ ℂ ℂ RealPlaces).prodCongr
      ((Algebra.TensorProduct.piRight ℝ ℂ ℂ (fun _ : ComplexPlaces => ℂ)).trans
        (AlgEquiv.piCongrRight (fun _ : ComplexPlaces => DeligneTorus.tensorSplitEquiv ℂ)))).trans
      (flattenPlaceFactors F))

/-- The coefficient at a place before scalar extension. The second coordinate
at a complex place is obtained by complex conjugation. -/
def complexifiedPlaceValue (x : mixedEmbedding.mixedSpace F) : ComplexifiedPlace F → ℂ
  | .inl v => (x.1 v : ℂ)
  | .inr (v, true) => x.2 v
  | .inr (v, false) => star (x.2 v)

@[simp]
theorem complexifiedScalarCoordinates_tmul (c : ℂ) (x : mixedEmbedding.mixedSpace F)
    (v : ComplexifiedPlace F) :
    complexifiedScalarCoordinates F (c ⊗ₜ[ℝ] x) v = c * complexifiedPlaceValue F x v := by
  rcases v with v | ⟨v, b⟩
  · change (x.1 v) • c = _
    rw [Complex.real_smul, mul_comm]
    rfl
  · cases b
    · change (DeligneTorus.tensorSplitEquiv ℂ (c ⊗ₜ[ℝ] x.2 v)).2 = _
      exact congrArg Prod.snd (ComplexMatrix.tensorSplitEquiv_tmul c (x.2 v))
    · change (DeligneTorus.tensorSplitEquiv ℂ (c ⊗ₜ[ℝ] x.2 v)).1 = _
      exact congrArg Prod.fst (ComplexMatrix.tensorSplitEquiv_tmul c (x.2 v))

variable (n : ℕ)

private def tensorMatrixCoordinates :
    (ℂ ⊗[ℝ] ArchimedeanMatrix F n) ≃ₐ[ℂ]
      Matrix (Fin n) (Fin n) (ComplexifiedPlace F → ℂ) :=
  (ComplexMatrix.tensorAlgEquiv ℝ ℂ (mixedEmbedding.mixedSpace F) n).trans
    (complexifiedScalarCoordinates F).mapMatrix

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

private theorem tensorMatrixCoordinates_map_lie (x y : ComplexLieAlgebra F n) :
    let e : ComplexLieAlgebra F n ≃ₗ[ℂ] Matrix (Fin n) (Fin n) (ComplexifiedPlace F → ℂ) :=
      (tensorMatrixCoordinates F n).toLinearEquiv
    e ⁅x, y⁆ = ⁅e x, e y⁆ := by
  intro e
  induction x using TensorProduct.inductionOn with
  | tmul c X =>
    induction y using TensorProduct.inductionOn with
    | tmul d Y =>
      rw [complexLieAlgebra_lie_tmul]
      let X' := realLieAlgebraToMatrix F n X
      let Y' := realLieAlgebraToMatrix F n Y
      let Xc : ℂ ⊗[ℝ] ArchimedeanMatrix F n := c ⊗ₜ[ℝ] X'
      let Yc : ℂ ⊗[ℝ] ArchimedeanMatrix F n := d ⊗ₜ[ℝ] Y'
      change tensorMatrixCoordinates F n
        ((c * d) ⊗ₜ[ℝ] realLieAlgebraToMatrix F n ⁅X, Y⁆) =
          tensorMatrixCoordinates F n Xc * tensorMatrixCoordinates F n Yc -
            tensorMatrixCoordinates F n Yc * tensorMatrixCoordinates F n Xc
      rw [← map_mul, ← map_mul, ← map_sub]
      congr 1
      dsimp only [Xc, Yc, X', Y']
      rw [realLieAlgebraToMatrix_lie, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_comm d c]
      exact TensorProduct.tmul_sub _ _ _
    | add y y' hy hy' =>
      simp only [LieRing.lie_add, map_add, hy, hy']
  | add x x' hx hx' =>
    simp only [LieRing.add_lie, map_add, hx, hx']

/-- Actual archimedean complexification in matrix coordinates over the
product of its complexified place fields. -/
def complexLieMatrixCoordinates :
    ComplexLieAlgebra F n ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) (ComplexifiedPlace F → ℂ) :=
  { (tensorMatrixCoordinates F n).toLinearEquiv with
    map_lie' := by
      intro x y
      exact tensorMatrixCoordinates_map_lie F n x y }

@[simp]
theorem complexLieMatrixCoordinates_tmul (c : ℂ) (X : RealLieAlgebra F n)
    (i j : Fin n) (v : ComplexifiedPlace F) :
    complexLieMatrixCoordinates F n (c ⊗ₜ[ℝ] X) i j v =
      c * complexifiedPlaceValue F (realLieAlgebraToMatrix F n X i j) v := by
  change tensorMatrixCoordinates F n (c ⊗ₜ[ℝ] realLieAlgebraToMatrix F n X) i j v = _
  rw [tensorMatrixCoordinates, AlgEquiv.trans_apply, ComplexMatrix.tensorAlgEquiv_tmul]
  exact complexifiedScalarCoordinates_tmul F c _ v

end Langlands.Global.ArchimedeanGL
