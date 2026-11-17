import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Finite products of finite coordinate algebras -/

noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.AlgebraicGeometry.FiniteProductCoefficients

variable {α β : Type u}

section Coefficients

variable (A : α → Type u) [∀ a, CommRing (A a)] (I : α → Type u)

/-- The scalar algebra on finite coordinate families over each ring component. -/
@[instance_reducible]
def coefficientAlgebra : Algebra (∀ a, A a) (∀ a, I a → A a) := by
  letI (a : α) : Algebra (∀ b, A b) (A a) := (Pi.evalRingHom A a).toAlgebra
  infer_instance

/-- The scalar map sends a base family to the constant coordinate family in each
component; component ranks need not be constant. -/
def scalarMap : (∀ a, A a) →+* (∀ a, I a → A a) :=
  letI := coefficientAlgebra A I
  algebraMap _ _

@[simp] theorem scalarMap_apply (b : ∀ a, A a) (a : α) (i : I a) :
    scalarMap A I b a i = b a := rfl

variable [Finite α] [∀ a, Finite (I a)]

/-- The varying-rank coefficient algebra is finite over the product base. -/
theorem finite : (scalarMap A I).Finite := by
  classical
  letI (a : α) : Algebra (∀ b, A b) (A a) := (Pi.evalRingHom A a).toAlgebra
  haveI (a : α) : Module.Finite (∀ b, A b) (A a) :=
    RingHom.Finite.of_surjective (Pi.evalRingHom A a) (Function.surjective_eval a)
  haveI (a : α) : Module.Finite (∀ b, A b) (I a → A a) :=
    Module.Finite.trans (A a) (I a → A a)
  change Module.Finite (∀ a, A a) (∀ a, I a → A a)
  infer_instance

/-- Each product projection is a localization at an idempotent and hence étale;
finite coordinate products are therefore étale over the product base. -/
theorem etale : (scalarMap A I).Etale := by
  classical
  letI (a : α) : Algebra (∀ b, A b) (A a) := (Pi.evalRingHom A a).toAlgebra
  haveI (a : α) : IsLocalization.Away (Pi.single a 1 : ∀ b, A b) (A a) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom A a)
      (Function.surjective_eval a)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  haveI (a : α) : Algebra.Etale (∀ b, A b) (A a) :=
    Algebra.Etale.of_isLocalizationAway (Pi.single a 1)
  change Algebra.Etale (∀ a, A a) (∀ a, I a → A a)
  infer_instance

/-- The coefficient module is projective, even when some component ranks vanish. -/
theorem projective :
    letI := (scalarMap A I).toAlgebra
    Module.Projective (∀ a, A a) (∀ a, I a → A a) := by
  letI := (scalarMap A I).toAlgebra
  haveI : Module.Finite (∀ a, A a) (∀ a, I a → A a) := finite A I
  haveI : Algebra.Etale (∀ a, A a) (∀ a, I a → A a) := etale A I
  haveI : Module.FinitePresentation (∀ a, A a) (∀ a, I a → A a) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

end Coefficients

section Tensor

open scoped TensorProduct

variable (R : Type u) [CommRing R]

/-- Interchange two indices of a family of coefficient algebras. -/
def piSwap (M : α → β → Type u) [∀ a b, CommRing (M a b)]
    [∀ a b, Algebra R (M a b)] :
    (∀ a b, M a b) ≃ₐ[R] (∀ b a, M a b) where
  toFun z b a := z a b
  invFun z a b := z b a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (A : α → Type u) (B : β → Type u)
  [∀ a, CommRing (A a)] [∀ b, CommRing (B b)]
  [∀ a, Algebra R (A a)] [∀ b, Algebra R (B b)]
  [Finite α] [Finite β]

/-- Distribute a tensor product over finite products on both sides. -/
def tensorPi : ((∀ a, A a) ⊗[R] (∀ b, B b)) ≃ₐ[R]
    (∀ a b, A a ⊗[R] B b) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  exact (Algebra.TensorProduct.piRight R R (∀ a, A a) B).trans
    ((AlgEquiv.piCongrRight fun b =>
      (Algebra.TensorProduct.comm R (∀ a, A a) (B b)).trans
        ((Algebra.TensorProduct.piRight R R (B b) A).trans
          (AlgEquiv.piCongrRight fun a => Algebra.TensorProduct.comm R (B b) (A a)))).trans
      (piSwap R (fun b a => A a ⊗[R] B b)))

@[simp] theorem tensorPi_tmul (x : ∀ a, A a) (y : ∀ b, B b) (a : α) (b : β) :
    tensorPi R A B (x ⊗ₜ[R] y) a b = x a ⊗ₜ[R] y b := rfl

/-- The tensor extension of the varying-rank coefficient algebra is the family
of overlap tensor rings indexed by the target chart's coordinates. -/
def tensorCoefficients (I : α → Type u) [∀ a, Finite (I a)] :
    ((∀ a, A a) ⊗[R] (∀ a, I a → A a)) ≃ₐ[R]
      (∀ a b, I b → (A a ⊗[R] A b)) := by
  classical
  letI := Fintype.ofFinite α
  letI (a : α) := Fintype.ofFinite (I a)
  exact (tensorPi R A (fun b => I b → A b)).trans
    (AlgEquiv.piCongrRight fun a => AlgEquiv.piCongrRight fun b =>
      Algebra.TensorProduct.piRight R R (A a) (fun _ : I b => A b))

@[simp] theorem tensorCoefficients_tmul (I : α → Type u) [∀ a, Finite (I a)]
    (x : ∀ a, A a) (z : ∀ a, I a → A a) (a b : α) (i : I b) :
    tensorCoefficients R A I (x ⊗ₜ[R] z) a b i = x a ⊗ₜ[R] z b i := rfl

end Tensor
end Langlands.AlgebraicGeometry.FiniteProductCoefficients
