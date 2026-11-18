import Langlands.Geometry.FormalGroup.RationalSectionBaseChangeCalculus
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Nilpotent rigidity of local quasi-isogenies -/

universe v

namespace Langlands.FormalGroup.ModuleLaw
open TopologicalSpace

/-- The affine coordinated p-divisible case of nilpotent rigidity. The
map is pullback of the actual rational Hom sheaf along a nilpotent quotient. -/
def LocalQuasiIsogenyNilpotentRigidityStatement : Prop :=
  ∀ (R : Type v) [CommRing R] (p : ℕ), Nat.Prime p →
    ∀ (σ τ : Type) [Finite σ] [Finite τ]
      (M : ModuleLaw ℤ R σ) (N : ModuleLaw ℤ R τ)
      (I : Ideal R), IsNilpotent I →
      M.IsPiDivisible (p : ℤ) → N.IsPiDivisible (p : ℤ) →
        ∀ U : Opens (PrimeSpectrum R),
          Function.Bijective
            (fun z : LocalQuasiIsogeny (ULift.{v} ℚ) (p : ℤ) M N U =>
              z.baseChange (Ideal.Quotient.mkₐ ℤ I))

end Langlands.FormalGroup.ModuleLaw
