import Langlands.Algebra.SeparatedEnvelopingSymmetrization
import Langlands.Global.ArchimedeanSymmetricAlgebraSymmetrization

/-! # Actual Cartan and compact separated symmetrization -/

noncomputable section
universe u
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Symmetrization along the actual complex Cartan-complement inclusion. -/
def cartanSymmetricAlgebraSymmetrize :
    CartanSymmetricAlgebra K n →ₗ[ℂ] EnvelopingAlgebra K n :=
  (lieSymmetricAlgebraSymmetrize K n).comp
    (cartanSymmetricInclusion K n).toLinearMap

@[simp]
theorem cartanSymmetricAlgebraSymmetrize_apply (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricAlgebraSymmetrize K n P =
      lieSymmetricAlgebraSymmetrize K n (cartanSymmetricInclusion K n P) := rfl

@[simp]
theorem cartanSymmetricAlgebraSymmetrize_ι (X : ComplexCartanComplement K n) :
    cartanSymmetricAlgebraSymmetrize K n (SymmetricAlgebra.ι ℂ _ X) =
      envelopingGenerator K n (cartanComplexInclusion K n X) := by
  simp

/-- The actual Lie directions split into complementary vectors and vectors whose
generators belong to the genuine compact enveloping subalgebra. -/
theorem cartanCompact_envelopingGenerator_split :
    LinearMap.range (cartanComplexInclusion K n) ⊔
      (compactEnvelopingSubalgebra K n).toSubmodule.comap
        (envelopingGenerator K n).toLinearMap = ⊤ := by
  apply top_unique
  intro X hX
  clear hX
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    apply Submodule.mem_sup.mpr
    refine ⟨cartanComplexInclusion K n (z ⊗ₜ[ℝ] cartanComplementProjection K n X),
      ⟨z ⊗ₜ[ℝ] cartanComplementProjection K n X, rfl⟩,
      compactComplexInclusion K n (z ⊗ₜ[ℝ] compactProjection K n X), ?_, ?_⟩
    · exact compactEnvelopingGenerator_mem K n (z ⊗ₜ[ℝ] compactProjection K n X)
    · change z ⊗ₜ[ℝ] (cartanComplementProjection K n X : RealLieAlgebra K n) +
          z ⊗ₜ[ℝ] (compactProjection K n X : RealLieAlgebra K n) = z ⊗ₜ[ℝ] X
      rw [← TensorProduct.tmul_add, add_comm,
        compactProjection_add_cartanComplementProjection]
  | add X Y hX hY => exact Submodule.add_mem _ hX hY

/-- Multiply a symmetrized actual Cartan tensor by a genuine compact enveloping element. -/
def cartanCompactSymmetrization :
    CartanSymmetricAlgebra K n ⊗[ℂ] compactEnvelopingSubalgebra K n →ₗ[ℂ]
      EnvelopingAlgebra K n :=
  Langlands.Algebra.UniversalEnveloping.separatedSymmetrization ℂ
    (ComplexLieAlgebra K n) (cartanComplexInclusion K n) (compactEnvelopingSubalgebra K n)

@[simp]
theorem cartanCompactSymmetrization_tmul (P : CartanSymmetricAlgebra K n)
    (b : compactEnvelopingSubalgebra K n) :
    cartanCompactSymmetrization K n (P ⊗ₜ[ℂ] b) =
      cartanSymmetricAlgebraSymmetrize K n P * (b : EnvelopingAlgebra K n) := rfl

/-- The ordered Cartan-symmetric/compact-enveloping tensor map spans the entire
actual enveloping algebra. -/
theorem cartanCompactSymmetrization_surjective :
    Function.Surjective (cartanCompactSymmetrization K n) :=
  Langlands.Algebra.UniversalEnveloping.separatedSymmetrization_surjective ℂ
    (ComplexLieAlgebra K n) (cartanComplexInclusion K n) (compactEnvelopingSubalgebra K n)
    (cartanCompact_envelopingGenerator_split K n)

theorem cartanSymmetricAlgebraSymmetrize_conjugation (k : standardInfiniteCompact K n)
    (P : CartanSymmetricAlgebra K n) :
    envelopingConjugation K n k.val (cartanSymmetricAlgebraSymmetrize K n P) =
      cartanSymmetricAlgebraSymmetrize K n (cartanSymmetricConjugation K n k P) := by
  simp only [cartanSymmetricAlgebraSymmetrize_apply,
    lieSymmetricAlgebraSymmetrize_conjugation, cartanSymmetricInclusion_conjugation]

end Langlands.Global.ArchimedeanGL
