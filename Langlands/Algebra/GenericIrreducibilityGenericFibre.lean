import Langlands.Algebra.GenericIrreducibilityAffineModel
import Mathlib.RingTheory.Unramified.Field

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open scoped TensorProduct IntermediateField

namespace Langlands.Algebra.GenericIrreducibilitySpreading

/-- Injective ring maps reflect the primality of the nilradical. -/
theorem nilradical_isPrime_of_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (hB : (nilradical B).IsPrime) :
    (nilradical A).IsPrime := by
  have heq : (nilradical B).comap f = nilradical A := by
    ext x
    simp only [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  rw [← heq]
  exact hB.comap f

/-- Geometric irreducibility of a field tensor forces separable constants to be scalars. -/
theorem forall_isSeparable_mem_range_of_tensor_nilradical_isPrime
    {F : Type u} {L : Type v} {Ω : Type w}
    [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [IsAlgClosed Ω]
    (hgen : (nilradical (Ω ⊗[F] L)).IsPrime) :
    ∀ θ : L, IsSeparable F θ → θ ∈ (algebraMap F L).range := by
  intro θ hθ
  let T := F⟮θ⟯
  let : CommRing (Ω ⊗[F] T) := inferInstance
  have : FiniteDimensional F T := IntermediateField.adjoin.finiteDimensional hθ.isIntegral
  have : Algebra.IsSeparable F T :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F L).mpr hθ
  have : Algebra.FormallyUnramified F T := Algebra.FormallyUnramified.of_isSeparable F T
  let i : Ω ⊗[F] T →ₐ[F] Ω ⊗[F] L :=
    Algebra.TensorProduct.map (AlgHom.id F Ω) (IntermediateField.val T)
  have hi : Function.Injective i := by
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := Ω)
      (IntermediateField.val T).toLinearMap Subtype.val_injective
  have hp := nilradical_isPrime_of_injective
    (A := Ω ⊗[F] T) (B := Ω ⊗[F] L) i.toRingHom hi hgen
  have : IsReduced (Ω ⊗[F] T) :=
    Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[F] T)
  have : (⊥ : Ideal (Ω ⊗[F] T)).IsPrime := by
    rw [nilradical_eq_zero] at hp
    with_reducible_and_instances exact hp
  have : IsDomain (Ω ⊗[F] T) := IsDomain.of_bot_isPrime _
  have hbij : Function.Bijective (algebraMap Ω (Ω ⊗[F] T)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hdim : Module.finrank F T = 1 := by
    rw [← Module.finrank_baseChange (R := Ω)]
    exact Module.finrank_of_bijective_algebraMap hbij
  exact IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hdim

/-- The field-tensor generic hypothesis discharges the separable-constant premise
of the domain spreading core. -/
theorem exists_ne_zero_tensor_nilradical_isPrime_of_fractionFieldTensor
    {R : Type u} {C : Type v} {Ω : Type t}
    [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C]
    [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] [IsAlgClosed Ω]
    (hgen :
      letI : Algebra (FractionRing R) (FractionRing C) :=
        FractionRing.liftAlgebra R (FractionRing C)
      letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
      (nilradical (Ω ⊗[FractionRing R] FractionRing C)).IsPrime) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
      algebraMap R K a ≠ 0 → (nilradical (K ⊗[R] C)).IsPrime := by
  apply exists_ne_zero_tensor_nilradical_isPrime_of_separablyClosed_range
  let : Algebra (FractionRing R) (FractionRing C) :=
    FractionRing.liftAlgebra R (FractionRing C)
  let : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  exact forall_isSeparable_mem_range_of_tensor_nilradical_isPrime hgen

end Langlands.Algebra.GenericIrreducibilitySpreading
