import Langlands.CommutativeAlgebra.SquareZeroCotangentCoefficients

/-! # Descent of coefficient automorphisms to a quotient base -/

noncomputable section

universe u

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.CommutativeAlgebra

section Scalars

variable {A S X Y : Type u} [CommSemiring A] [Semiring S] [Algebra A S]
variable [AddCommMonoid X] [Module A X] [Module S X] [IsScalarTower A S X]
variable [AddCommMonoid Y] [Module A Y] [Module S Y] [IsScalarTower A S Y]

/-- A linear equivalence over a ring surjecting onto the acting algebra is
already linear over that algebra. -/
def linearEquivOfSurjectiveAlgebra (h : Function.Surjective (algebraMap A S))
    (e : X ≃ₗ[A] Y) : X ≃ₗ[S] Y where
  __ := e.toAddEquiv
  map_smul' s x := by
    obtain ⟨a, rfl⟩ := h s
    change e ((algebraMap A S a) • x) = (algebraMap A S a) • e x
    simpa only [algebraMap_smul] using e.map_smul a x

end Scalars

namespace QuotientCoefficients

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]
  [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]
variable (B : Type u) [CommRing B] [Algebra R B]

local instance quotientTestRightAlgebra : Algebra B ((R ⧸ I) ⊗[R] B) :=
  Algebra.TensorProduct.rightAlgebra

/-- The test algebra maps onto its quotient-base scalar extension. -/
theorem quotientTest_surjective :
    Function.Surjective (algebraMap B ((R ⧸ I) ⊗[R] B)) :=
  Algebra.TensorProduct.includeRight_surjective B (show Function.Surjective
    (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

/-- Canonical rearrangement of a quotient-base module's coefficients on an
actual base-changed test algebra. -/
def coefficientEquiv :
    (((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) ≃ₗ[B] B ⊗[R] M :=
  Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.coefficientTensorEquiv

/-- Every coefficient-algebra-linear automorphism of the original extended
module descends to an automorphism linear over the actual quotient test algebra. -/
def descendAutomorphism (e : B ⊗[R] M ≃ₗ[B] B ⊗[R] M) :
    (((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) ≃ₗ[(R ⧸ I) ⊗[R] B]
      (((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) :=
  linearEquivOfSurjectiveAlgebra (A := B) (S := (R ⧸ I) ⊗[R] B)
    (quotientTest_surjective I B)
    ((coefficientEquiv I M B).trans (e.trans (coefficientEquiv I M B).symm))

/-- The descended automorphism is characterized by the original action after
coefficient rearrangement. -/
theorem descendAutomorphism_apply (e : B ⊗[R] M ≃ₗ[B] B ⊗[R] M)
    (z : ((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) :
    coefficientEquiv I M B (descendAutomorphism I M B e z) =
      e (coefficientEquiv I M B z) := by
  change coefficientEquiv I M B
    ((coefficientEquiv I M B).symm (e (coefficientEquiv I M B z))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Descending coefficients preserves identities and composition of linear
automorphisms. -/
def descendAutomorphismHom :
    (B ⊗[R] M ≃ₗ[B] B ⊗[R] M) →*
      ((((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) ≃ₗ[(R ⧸ I) ⊗[R] B]
        (((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M)) where
  toFun := descendAutomorphism I M B
  map_one' := by
    apply LinearEquiv.ext
    intro z
    apply (coefficientEquiv I M B).injective
    rw [descendAutomorphism_apply]
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro z
    apply (coefficientEquiv I M B).injective
    change coefficientEquiv I M B (descendAutomorphism I M B (e * f) z) =
      coefficientEquiv I M B
        (descendAutomorphism I M B e (descendAutomorphism I M B f z))
    rw [descendAutomorphism_apply, descendAutomorphism_apply, descendAutomorphism_apply]
    rfl

variable {B} {C : Type u} [CommRing C] [Algebra R C]

/-- Coefficient rearrangement is natural under every algebra map. -/
theorem coefficientEquiv_naturality (f : B →ₐ[R] C)
    (z : ((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) :
    coefficientEquiv I M C
      (TensorProduct.map (SquareZero.quotientTestMap I f).toLinearMap LinearMap.id z) =
      TensorProduct.map f.toLinearMap LinearMap.id (coefficientEquiv I M B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t m =>
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        SquareZero.quotientTestMap_tmul, LinearMap.id_apply, coefficientEquiv,
        Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.coefficientTensorEquiv_tmul]
    | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Compatible original coefficient automorphisms give compatible descended
quotient-base automorphisms. -/
theorem descendAutomorphism_naturality (f : B →ₐ[R] C)
    (eB : B ⊗[R] M ≃ₗ[B] B ⊗[R] M) (eC : C ⊗[R] M ≃ₗ[C] C ⊗[R] M)
    (he : ∀ x, TensorProduct.map f.toLinearMap LinearMap.id (eB x) =
      eC (TensorProduct.map f.toLinearMap LinearMap.id x))
    (z : ((R ⧸ I) ⊗[R] B) ⊗[R ⧸ I] M) :
    TensorProduct.map (SquareZero.quotientTestMap I f).toLinearMap LinearMap.id
        (descendAutomorphism I M B eB z) =
      descendAutomorphism I M C eC
        (TensorProduct.map (SquareZero.quotientTestMap I f).toLinearMap LinearMap.id z) := by
  apply (coefficientEquiv I M C).injective
  rw [coefficientEquiv_naturality, descendAutomorphism_apply, he,
    descendAutomorphism_apply, coefficientEquiv_naturality]

end QuotientCoefficients

end Langlands.CommutativeAlgebra
