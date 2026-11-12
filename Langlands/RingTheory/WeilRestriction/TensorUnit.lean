import Langlands.RingTheory.WeilRestriction.Functorial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Surjective coordinate map of the scalar-extension Weil unit -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.WeilRestrictionFiniteType

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [Module.Finite A B] [Module.Projective A B] [Algebra.FiniteType A C]

/-- The algebra map classifying the identity point of the scalar-extended algebra.
Its spectrum is the canonical unit into restriction after scalar extension. -/
def tensorUnit : WeilRestrictionFiniteType A B (B ⊗[A] C) →ₐ[A] C :=
  (homEquiv A B (B ⊗[A] C) C).symm (AlgHom.id B (B ⊗[A] C))

/-- Scalar extension of the unit has the universal point as a section. -/
theorem lTensor_tensorUnit_comp_universalPoint :
    (Algebra.TensorProduct.lTensor (S := B) B (tensorUnit A B C)).comp
        (universalPoint A B (B ⊗[A] C)) = AlgHom.id B (B ⊗[A] C) :=
  (homEquiv A B (B ⊗[A] C) C).apply_symm_apply _

theorem lTensor_tensorUnit_surjective :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := B) B (tensorUnit A B C)) := by
  intro x
  refine ⟨universalPoint A B (B ⊗[A] C) x, ?_⟩
  exact congrArg (fun f : B ⊗[A] C →ₐ[B] B ⊗[A] C => f x)
    (lTensor_tensorUnit_comp_universalPoint A B C)

/-- Faithful flatness descends the surjectivity of this canonical coordinate map. -/
theorem tensorUnit_surjective [Module.FaithfullyFlat A B] :
    Function.Surjective (tensorUnit A B C) := by
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B
    (tensorUnit A B C).toLinearMap).mp
  exact lTensor_tensorUnit_surjective A B C

variable {C} {D : Type*} [CommRing D] [Algebra A D] [Algebra.FiniteType A D]

/-- The coordinate unit is natural in the original finite-type algebra. -/
theorem tensorUnit_natural (f : C →ₐ[A] D) :
    (tensorUnit A B D).comp
        (map A B (Algebra.TensorProduct.lTensor (S := B) B f)) =
      f.comp (tensorUnit A B C) := by
  apply (homEquiv A B (B ⊗[A] C) D).injective
  rw [homEquiv_comp_map, homEquiv_comp]
  simp only [tensorUnit, Equiv.apply_symm_apply, AlgHom.id_comp, AlgHom.comp_id]

end Langlands.Algebra.WeilRestrictionFiniteType
