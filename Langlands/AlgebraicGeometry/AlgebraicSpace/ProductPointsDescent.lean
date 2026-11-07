import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Products of finite free algebras of uniform rank

Let `A i → B i` be a family of ring maps, each making `B i` free of rank `d` over `A i`, with a
chosen basis indexed by `Fin d`. Then `∏ B i` is free of rank `d` over `∏ A i`, and the tensor
square `(∏ B i) ⊗[∏ A i] (∏ B i)` is the product of the tensor squares `B i ⊗[A i] B i`.
This is the algebra behind the descent step in Conrad's proof of Proposition 5.2.
-/

noncomputable section

universe u

open TensorProduct Module

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ProductPointsDescent

section Basis

variable {ι : Type u} {A M : ι → Type u} [∀ i, CommRing (A i)] [∀ i, AddCommGroup (M i)]
  [∀ i, Module (A i) (M i)] {d : ℕ}

/-- A family of bases of uniform size gives a basis of the product module over the product
ring. -/
def piBasis (b : ∀ i, Basis (Fin d) (A i) (M i)) : Basis (Fin d) (∀ i, A i) (∀ i, M i) :=
  Basis.ofEquivFun
    { toFun := fun y k i => (b i).repr (y i) k
      invFun := fun c i => (b i).equivFun.symm (fun k => c k i)
      map_add' := fun y z => by
        ext k i
        simp
      map_smul' := fun r y => by
        ext k i
        simp
      left_inv := fun y => by
        ext i
        change (b i).equivFun.symm ((b i).equivFun (y i)) = y i
        exact (b i).equivFun.symm_apply_apply (y i)
      right_inv := fun c => by
        ext k i
        change (b i).equivFun ((b i).equivFun.symm (fun k => c k i)) k = c k i
        rw [(b i).equivFun.apply_symm_apply] }

theorem piBasis_apply (b : ∀ i, Basis (Fin d) (A i) (M i)) (k : Fin d) :
    piBasis b k = fun i => b i k := by
  classical
  ext i
  simp only [piBasis, Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
  change (b i).equivFun.symm (fun k' => (Pi.single k 1 : Fin d → ∀ i, A i) k' i) = b i k
  have : (fun k' => (Pi.single k 1 : Fin d → ∀ i, A i) k' i) = Pi.single k 1 := by
    ext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [h]
  rw [this, Basis.equivFun_symm_single]

end Basis

section Tensor

variable {ι : Type u} (A B : ι → Type u) [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
  [∀ i, Algebra (A i) (B i)]

/-- The product of the tensor squares, as an algebra over `∏ B i` through the left factors. -/
abbrev TensorSquares : Type u := ∀ i, B i ⊗[A i] B i

/-- The left inclusion `∏ B i → ∏ (B i ⊗ B i)`. -/
def inl : (∀ i, B i) →ₐ[∀ i, A i] TensorSquares A B :=
  { toRingHom := RingHom.pi fun i =>
      (Algebra.TensorProduct.includeLeftRingHom (R := A i)).comp (Pi.evalRingHom B i)
    commutes' := fun r => funext fun i =>
      (Algebra.TensorProduct.includeLeft (R := A i) (S := A i) (A := B i) (B := B i)).commutes
        (r i) }

/-- The right inclusion `∏ B i → ∏ (B i ⊗ B i)`. -/
def inr : (∀ i, B i) →ₐ[∀ i, A i] TensorSquares A B :=
  { toRingHom := RingHom.pi fun i =>
      (Algebra.TensorProduct.includeRight (R := A i) (A := B i) (B := B i)).toRingHom.comp
        (Pi.evalRingHom B i)
    commutes' := fun r => funext fun i =>
      (Algebra.TensorProduct.includeRight (R := A i) (A := B i) (B := B i)).commutes (r i) }

@[simp] theorem inl_apply (y : ∀ i, B i) (i : ι) : inl A B y i = y i ⊗ₜ 1 := rfl

@[simp] theorem inr_apply (y : ∀ i, B i) (i : ι) : inr A B y i = 1 ⊗ₜ y i := rfl

/-- The comparison map `(∏ B i) ⊗[∏ A i] (∏ B i) → ∏ (B i ⊗ B i)`. -/
def comparison : (∀ i, B i) ⊗[∀ i, A i] (∀ i, B i) →ₐ[∀ i, A i] TensorSquares A B :=
  Algebra.TensorProduct.productMap (inl A B) (inr A B)

@[simp] theorem comparison_tmul (x y : ∀ i, B i) (i : ι) :
    comparison A B (x ⊗ₜ y) i = x i ⊗ₜ y i := by
  simp [comparison, Algebra.TensorProduct.tmul_mul_tmul]

variable {A B}

/-- With uniform bases, the comparison map is bijective. -/
theorem comparison_bijective {d : ℕ} (b : ∀ i, Basis (Fin d) (A i) (B i)) :
    Function.Bijective (comparison A B) := by
  classical
  -- the basis of the source over the left factor
  let bR := piBasis b
  let bT : Basis (Fin d) (∀ i, B i) ((∀ i, B i) ⊗[∀ i, A i] (∀ i, B i)) :=
    Algebra.TensorProduct.basis (∀ i, B i) bR
  -- the basis of the target over the left factor, through `inl`
  let bP : Basis (Fin d) (∀ i, B i) (TensorSquares A B) :=
    piBasis fun i => Algebra.TensorProduct.basis (B i) (b i)
  -- the comparison map is linear over the left factor
  let φ : ((∀ i, B i) ⊗[∀ i, A i] (∀ i, B i)) →ₗ[∀ i, B i] TensorSquares A B :=
    { toFun := comparison A B
      map_add' := map_add _
      map_smul' := fun c t => by
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          ext i
          rw [TensorProduct.smul_tmul', comparison_tmul]
          show (c * x) i ⊗ₜ y i = c i • comparison A B (x ⊗ₜ y) i
          rw [comparison_tmul, TensorProduct.smul_tmul']
          rfl
        | add t₁ t₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂, RingHom.id_apply] }
  have hφ : ∀ k, φ (bT k) = bP k := by
    intro k
    simp only [bT, bP, Algebra.TensorProduct.basis_apply, piBasis_apply]
    ext i
    change comparison A B (1 ⊗ₜ bR k) i = _
    rw [comparison_tmul, piBasis_apply]
    rfl
  have he : φ = (bP.equiv bT (Equiv.refl _)).symm.toLinearMap := by
    apply bT.ext
    intro k
    rw [hφ]
    simp [Basis.equiv_symm, Basis.equiv_apply]
  have : Function.Bijective φ := by
    rw [he]
    exact (bP.equiv bT (Equiv.refl _)).symm.bijective
  exact this

end Tensor

end ProductPointsDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace
