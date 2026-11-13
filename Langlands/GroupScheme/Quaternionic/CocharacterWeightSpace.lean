import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Quaternionic.TensorMatrixComparison
import Langlands.GroupScheme.MultiplicativePointTopology

/-!
# Weight spaces of a cocharacter of `O(q)` on the row space `D^n`

For a cocharacter `f : 𝔾_m ⟶ O(q)` of the isometry group of a `σ`-quadratic form and an
integer `c`, `cocharacterWeightSpace q f c` is the left `D`-subspace of row vectors
`v ∈ D^n` on which `f` acts through the character `t ↦ t^c`. The row action is the one
used throughout the Library: a point `u` of `O(q)` acts by inverse right multiplication
`v ↦ v u⁻¹`. The condition is imposed on points with values in every commutative
`K`-algebra.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- The unit of `R ⊗[K] M_n(D)` underlying a point of `O(q)` with values in a commutative
`K`-algebra `R`, read through the closed inclusion of `O(q)` into the unit group scheme. -/
def isometryAffineUnitsOver (q : σ.QuadraticForms n) (R : CommAlgCat.{u} (CommRingCat.of K)) :
    GroupScheme.affinePoints (σ.isometryGroup q) R →* (R ⊗[K] Matrix n n D)ˣ :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R).toMonoidHom.comp
    ((σ.isometryGroup q).affinePointsTarget (σ.isometryGroupι q) R)

/-- The weight space of weight `c` of a cocharacter `f : 𝔾_m ⟶ O(q)` on the row space
`D^n`: the row vectors `v` such that, for every commutative `K`-algebra `R` and every
point `t ∈ 𝔾_m(R) = Rˣ`, inverse right multiplication by the unit of `f(t)` sends
`1 ⊗ v` to `t^c ⊗ v` in `(R ⊗[K] D)^n`. -/
def cocharacterWeightSpace (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) (c : ℤ) :
    Submodule D (n → D) where
  carrier := {v | ∀ (R : CommAlgCat.{u} (CommRingCat.of K))
      (t : GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp R),
      Matrix.vecMul (fun i => (1 : R) ⊗ₜ[K] v i)
          (TensorMatrix.equiv R n
            (((σ.isometryAffineUnitsOver q R (t ≫ f.hom.hom))⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
              R ⊗[K] Matrix n n D)) =
        (fun i => (((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ c : Rˣ) : R) ⊗ₜ[K] v i))}
  add_mem' := by
    intro v w hv hw R t
    have h1 := hv R t
    have h2 := hw R t
    have e1 : (fun i => (1 : R) ⊗ₜ[K] (v + w) i) =
        (fun i => (1 : R) ⊗ₜ[K] v i) + fun i => (1 : R) ⊗ₜ[K] w i := by
      ext i; simp [TensorProduct.tmul_add]
    rw [e1, Matrix.add_vecMul, h1, h2]
    ext i; simp [TensorProduct.tmul_add]
  zero_mem' := by
    intro R t
    simp only [Pi.zero_apply, TensorProduct.tmul_zero]
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro a v hv R t
    have h := hv R t
    have e1 : (fun i => (1 : R) ⊗ₜ[K] (a • v) i) =
        fun i => ((1 : R) ⊗ₜ[K] a) * ((1 : R) ⊗ₜ[K] v i) := by
      ext i; simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1]
    have e2 : Matrix.vecMul (fun i => ((1 : R) ⊗ₜ[K] a) * ((1 : R) ⊗ₜ[K] v i))
        (TensorMatrix.equiv R n
            (((σ.isometryAffineUnitsOver q R (t ≫ f.hom.hom))⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
              R ⊗[K] Matrix n n D)) =
        fun j => ((1 : R) ⊗ₜ[K] a) * Matrix.vecMul (fun i => (1 : R) ⊗ₜ[K] v i)
          (TensorMatrix.equiv R n
            (((σ.isometryAffineUnitsOver q R (t ≫ f.hom.hom))⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
              R ⊗[K] Matrix n n D)) j := by
      ext j
      simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    rw [e2, h]
    ext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
