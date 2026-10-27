import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Trace.Basic

/-! # Exact trace images of ideal powers in an extension of DVRs -/

namespace Langlands.LocalField

universe uA uB uK uL

/-- An extension of domains whose fraction-field maps form compatible towers is
torsion-free: the map `A → B` is injective because `A → K → L` is injective and
equals `A → B → L`. -/
theorem isTorsionFree_of_isFractionRing_tower
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
    Module.IsTorsionFree A B := by
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
  intro x y hxy
  apply IsFractionRing.injective A K
  apply (algebraMap K L).injective
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L y, hxy]

/-- For a finite extension of DVRs whose fraction-field extension is finite and
separable, with ramification index `e` and actual different `mB ^ d`, the trace
image of `mB ^ n` is exactly `mA ^ ((d + n) / e)`, as a set of elements of `K`. -/
def DVRTraceIdeals : Prop :=
  ∀ (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    [Module.Finite A B],
    haveI := isTorsionFree_of_isFractionRing_tower A B K L
    ∀ e d : ℕ, 0 < e →
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        (IsLocalRing.maximalIdeal B) ^ e →
      differentIdeal A B = (IsLocalRing.maximalIdeal B) ^ d →
      ∀ n : ℕ,
        let r := (d + n) / e
        ∀ y : K,
          (∃ x : B, x ∈ (IsLocalRing.maximalIdeal B) ^ n ∧
            Algebra.trace K L (algebraMap B L x) = y) ↔
          (∃ a : A, a ∈ (IsLocalRing.maximalIdeal A) ^ r ∧ algebraMap A K a = y)

end Langlands.LocalField
