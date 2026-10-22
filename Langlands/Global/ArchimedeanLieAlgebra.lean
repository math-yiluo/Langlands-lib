import Langlands.Global.ArchimedeanGL
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The concrete archimedean matrix Lie algebra and its complexification

The real Lie algebra is the actual matrix algebra with bracket `X * Y - Y * X`.
Its complexification is a scalar-extension tensor product, and its enveloping
algebra is Mathlib's universal enveloping algebra.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- The real matrix Lie algebra, kept as a type synonym to fix its commutator
bracket independently of the function-space presentation of matrices. -/
def RealLieAlgebra : Type u := ArchimedeanMatrix K n

instance : LieRing (RealLieAlgebra K n) :=
  LieRing.ofAssociativeRing (A := ArchimedeanMatrix K n)

instance : LieAlgebra ℝ (RealLieAlgebra K n) :=
  LieAlgebra.ofAssociativeAlgebra (R := ℝ) (A := ArchimedeanMatrix K n)

/-- The real Lie algebra has exactly the underlying vector space of actual matrices. -/
def realLieAlgebraToMatrix : RealLieAlgebra K n ≃ₗ[ℝ] ArchimedeanMatrix K n :=
  LinearEquiv.refl ℝ (ArchimedeanMatrix K n)

@[simp]
theorem realLieAlgebraToMatrix_lie (X Y : RealLieAlgebra K n) :
    realLieAlgebraToMatrix K n ⁅X, Y⁆ =
      realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y -
        realLieAlgebraToMatrix K n Y * realLieAlgebraToMatrix K n X := rfl

/-- Scalar extension of the real matrix Lie algebra, including both real directions
at each complex infinite place. -/
abbrev ComplexLieAlgebra := ℂ ⊗[ℝ] RealLieAlgebra K n


@[simp]
theorem complexLieAlgebra_lie_tmul (z w : ℂ) (X Y : RealLieAlgebra K n) :
    ⁅z ⊗ₜ[ℝ] X, w ⊗ₜ[ℝ] Y⁆ = (z * w) ⊗ₜ[ℝ] ⁅X, Y⁆ :=
  LieAlgebra.ExtendScalars.bracket_tmul ℝ ℂ (RealLieAlgebra K n) (RealLieAlgebra K n) z w X Y

/-- The canonical real Lie homomorphism into the complexification. -/
def complexify : RealLieAlgebra K n →ₗ⁅ℝ⁆ ComplexLieAlgebra K n :=
  { TensorProduct.mk ℝ ℂ (RealLieAlgebra K n) 1 with
    map_lie' := by
      intro X Y
      change (1 : ℂ) ⊗ₜ[ℝ] ⁅X, Y⁆ = ⁅(1 : ℂ) ⊗ₜ[ℝ] X, (1 : ℂ) ⊗ₜ[ℝ] Y⁆
      rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] }

@[simp]
theorem complexify_apply (X : RealLieAlgebra K n) :
    complexify K n X = (1 : ℂ) ⊗ₜ[ℝ] X := rfl

/-- The actual universal enveloping algebra over the complex numbers. -/
abbrev EnvelopingAlgebra := UniversalEnvelopingAlgebra ℂ (ComplexLieAlgebra K n)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical Lie generators of the universal enveloping algebra. -/
def envelopingGenerator : ComplexLieAlgebra K n →ₗ⁅ℂ⁆ EnvelopingAlgebra K n :=
  UniversalEnvelopingAlgebra.ι ℂ

/-- The defining commutator relation in the genuine universal enveloping algebra. -/
theorem envelopingGenerator_lie (X Y : ComplexLieAlgebra K n) :
    envelopingGenerator K n ⁅X, Y⁆ =
      envelopingGenerator K n X * envelopingGenerator K n Y -
        envelopingGenerator K n Y * envelopingGenerator K n X :=
  (envelopingGenerator K n).map_lie X Y

/-- The actual algebra center, rather than the center of the matrix Lie algebra. -/
abbrev EnvelopingCenter := ↥(Subalgebra.center ℂ (EnvelopingAlgebra K n))

/-- Inclusion of the center into the actual enveloping algebra. -/
def centerInclusion : EnvelopingCenter K n →ₐ[ℂ] EnvelopingAlgebra K n :=
  (Subalgebra.center ℂ (EnvelopingAlgebra K n)).val

@[simp]
theorem centerInclusion_apply (z : EnvelopingCenter K n) :
    centerInclusion K n z = z.val := rfl

theorem centerInclusion_commute (z : EnvelopingCenter K n) (a : EnvelopingAlgebra K n) :
    a * centerInclusion K n z = centerInclusion K n z * a :=
  Subalgebra.mem_center_iff.mp z.property a

end Langlands.Global.ArchimedeanGL
