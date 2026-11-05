import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Analysis.Complex.Basic

/-! # Actual complexification and enveloping equivalences -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.LieEnvelopingEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℝ L]
  [LieRing L'] [LieAlgebra ℝ L']

/-- Complexification of an actual real Lie algebra equivalence. -/
def complex (e : L ≃ₗ⁅ℝ⁆ L') : ℂ ⊗[ℝ] L ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] L' :=
  { TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) e.toLinearEquiv with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) e.toLieHom).map_lie X Y }

@[simp]
theorem complex_tmul (e : L ≃ₗ⁅ℝ⁆ L') (z : ℂ) (X : L) :
    complex e (z ⊗ₜ[ℝ] X) = z ⊗ₜ[ℝ] e X := rfl

section Enveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A B : Type*} [CommRing R] [LieRing A] [LieAlgebra R A]
  [LieRing B] [LieAlgebra R B]

/-- The actual universal enveloping map induced by a Lie homomorphism. -/
def map (e : A →ₗ⁅R⁆ B) :
    UniversalEnvelopingAlgebra R A →ₐ[R] UniversalEnvelopingAlgebra R B :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp e)

@[simp]
theorem map_generator (e : A →ₗ⁅R⁆ B) (X : A) :
    map e (UniversalEnvelopingAlgebra.ι R X) =
      UniversalEnvelopingAlgebra.ι R (e X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply R _ X

/-- An actual Lie equivalence induces an equivalence of actual enveloping algebras. -/
def enveloping (e : A ≃ₗ⁅R⁆ B) :
    UniversalEnvelopingAlgebra R A ≃ₐ[R] UniversalEnvelopingAlgebra R B := by
  refine AlgEquiv.ofAlgHom (map e.toLieHom) (map e.symm.toLieHom) ?_ ?_
  · apply UniversalEnvelopingAlgebra.hom_ext
    ext X
    simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
      map_generator, LieEquiv.coe_coe, e.apply_symm_apply, AlgHom.id_apply]
  · apply UniversalEnvelopingAlgebra.hom_ext
    ext X
    simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
      map_generator, LieEquiv.coe_coe, e.symm_apply_apply, AlgHom.id_apply]

@[simp]
theorem enveloping_generator (e : A ≃ₗ⁅R⁆ B) (X : A) :
    enveloping e (UniversalEnvelopingAlgebra.ι R X) =
      UniversalEnvelopingAlgebra.ι R (e X) :=
  map_generator e.toLieHom X

end Enveloping

section Center

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]

/-- Restrict an actual algebra equivalence to its actual associative centers. -/
def center (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  ((Subalgebra.center R A).equivMapOfInjective e.toAlgHom e.injective).trans
    (Subalgebra.equivOfEq _ _ (Subalgebra.map_center_eq e))

@[simp]
theorem center_apply (e : A ≃ₐ[R] B) (z : Subalgebra.center R A) :
    (center e z).val = e z.val := rfl

end Center

end Langlands.Algebra.LieEnvelopingEquiv
