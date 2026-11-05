import Langlands.Algebra.GenericIrreducibilityReduction
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u v w t

open scoped TensorProduct

namespace Langlands.Algebra.GenericIrreducibilityReduction

/-- A nontrivial localization preserves primality of the nilradical. -/
theorem nilradical_isPrime_of_localization
    {A B : Type*} [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B]
    (hA : (nilradical A).IsPrime) : (nilradical B).IsPrime := by
  have hd : Disjoint (M : Set A) (nilradical A : Set A) := by
    rw [Set.disjoint_left]
    intro x hxM hx
    have hn := (mem_nilradical.mp hx).map (algebraMap A B)
    exact (IsLocalization.map_units B (⟨x, hxM⟩ : M)).not_isNilpotent hn
  have hp := IsLocalization.isPrime_of_isPrime_disjoint M B (nilradical A) hA hd
  change ((⊥ : Ideal A).radical.map (algebraMap A B)).IsPrime at hp
  rw [IsLocalization.map_radical M B] at hp
  change ((⊥ : Ideal A).map (algebraMap A B)).radical.IsPrime at hp
  rw [Ideal.map_bot] at hp
  exact hp

/-- Passing from a domain algebra to its fraction field preserves geometric
irreducibility over any fraction field of the base. -/
theorem nilradical_tensor_fractionField_isPrime
    {R : Type u} {C : Type v} {F : Type w} {L : Type t} {Ω : Type*}
    [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Field F] [Field L] [Field Ω]
    [Algebra R C] [Algebra R F] [IsFractionRing R F]
    [Algebra C L] [IsFractionRing C L] [Algebra R L] [IsScalarTower R C L]
    [Algebra F L] [IsScalarTower R F L]
    [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]
    (hgen : (nilradical (Ω ⊗[R] C)).IsPrime) :
    (nilradical (Ω ⊗[F] L)).IsPrime := by
  let e : Ω ⊗[F] L ≃ₐ[F] Ω ⊗[R] L :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors R) F Ω L
  have : Nontrivial (Ω ⊗[R] L) := e.symm.toRingHom.domain_nontrivial
  let j : Ω ⊗[R] C →ₐ[R] Ω ⊗[R] L :=
    Algebra.TensorProduct.map (AlgHom.id R Ω) (IsScalarTower.toAlgHom R C L)
  let : Algebra (Ω ⊗[R] C) (Ω ⊗[R] L) := j.toRingHom.toAlgebra
  have : IsScalarTower Ω (Ω ⊗[R] C) (Ω ⊗[R] L) :=
    .of_algebraMap_eq <| by
      intro x
      simp [j, RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right R Ω
    (nonZeroDivisors C) L (by
      ext x
      simp [j, RingHom.algebraMap_toAlgebra])
  have hp : (nilradical (Ω ⊗[R] L)).IsPrime :=
    nilradical_isPrime_of_localization
      ((nonZeroDivisors C).map (Algebra.TensorProduct.includeRight (R := R) (A := Ω)))
      hgen
  exact (nilradical_isPrime_iff_of_ringEquiv e.toRingEquiv).mpr hp

end Langlands.Algebra.GenericIrreducibilityReduction
