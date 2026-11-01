import Langlands.AlgebraicGeometry.NoetherianApproximation.InseparableNormalization
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

universe u v

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- A finite normal subbase of finite type over the integers suffices for finite
normalization; no separability assumption is needed. -/
theorem finite_normalization_of_normal_finite_subbase
    (B : Type v) (A : Type u)
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra.FiniteType ℤ B] [CommRing A] [IsDomain A]
    [Algebra B A] [FaithfulSMul B A] [Module.Finite B A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  let : Algebra (FractionRing B) (FractionRing A) :=
    FractionRing.liftAlgebra B (FractionRing A)
  have : Module.Finite B (integralClosure B (FractionRing A)) :=
    finite_integralClosure_of_normal_integer_finiteType B (FractionRing B) (FractionRing A)
  let i : integralClosure A (FractionRing A) →ₐ[B] integralClosure B (FractionRing A) :=
    Subalgebra.inclusion
      (show (integralClosure A (FractionRing A)).restrictScalars B ≤
          integralClosure B (FractionRing A) from
        fun x hx ↦ isIntegral_trans (R := B) x hx)
  have : Module.Finite B (integralClosure A (FractionRing A)) :=
    Module.Finite.of_injective i.toLinearMap
      (fun x y h ↦ by
        apply Subtype.ext
        exact congrArg
          (fun z : integralClosure B (FractionRing A) ↦ (z : FractionRing A)) h)
  exact Module.Finite.of_restrictScalars_finite B A _

/-- A finite type domain over a finite field has finite normalization. -/
theorem finite_normalization_of_finite_field
    (k : Type v) (A : Type u) [Field k] [Finite k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨s, f, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin s) k
  let : Algebra B A := f.toRingHom.toAlgebra
  have : Module.Finite ℤ k := inferInstance
  have : Algebra.FiniteType ℤ k := inferInstance
  have hB : Algebra.FiniteType ℤ B :=
    (inferInstance : Algebra.FiniteType ℤ (MvPolynomial (Fin s) k))
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  have : Module.Finite B A := hfin
  exact @finite_normalization_of_normal_finite_subbase B A _ _ _ _ hB _ _ _ _ _

/-- Positive-characteristic integer finite type domains have finite normalization. -/
theorem finite_normalization_of_prime_characteristic
    (A : Type u) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (p : ℕ) [Fact p.Prime] [CharP A p] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  have : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A
  exact finite_normalization_of_finite_field (ZMod p) A

end Langlands.AlgebraicGeometry.NoetherianApproximation
