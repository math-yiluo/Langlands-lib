import Langlands.CommutativeAlgebra.FiniteIntegralClosure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Finite separable extensions of a complete DVR -/

noncomputable section

open IsLocalRing
open ValuationTheory.DiscreteValuationField (CompleteDVF)

namespace Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]

local notation "B" => integralClosure R L

/-- The integral closure of a complete DVR in a finite separable fraction field
extension is a complete DVR. -/
theorem isDiscreteValuationRing_and_isAdicComplete
    [IsAdicComplete (maximalIdeal R) R] [FiniteDimensional (FractionRing R) L]
    [Algebra.IsSeparable (FractionRing R) L] :
    ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B := by
  let K := FractionRing R
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  let S := v.valuationSubring
  let e : R ≃+* S := IsDiscreteValuationRing.equivValuationSubring (A := R) (K := K)
  have hcS : IsAdicComplete (maximalIdeal S) S := by
    simpa only [IsLocalRing.map_ringEquiv_maximalIdeal] using
      (IsAdicComplete.congr_ringEquiv (maximalIdeal R) e).mpr
        (inferInstance : IsAdicComplete (maximalIdeal R) R)
  let base : CompleteDVF K :=
    { ValueGroup := _
      valuation := v
      instCompleteDiscrete := { isAdicComplete := hcS } }
  let : Algebra R S := e.toRingHom.toAlgebra
  have : IsScalarTower R S L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply S K L]
    rfl
  have : Algebra.IsIntegral R S :=
    algebraMap_isIntegral_iff.mp
      (RingHom.isIntegral_of_surjective (algebraMap R S) e.surjective)
  have hsame : integralClosure R L = (integralClosure S L).restrictScalars R := by
    ext x
    change IsIntegral R x ↔ IsIntegral S x
    exact ⟨IsIntegral.tower_top, isIntegral_trans (R := R) (A := ↥S) x⟩
  let C := integralClosure S L
  let eB : B ≃+* C := (Subalgebra.equivOfEq _ _ hsame).toRingEquiv
  have : IsDiscreteValuationRing C :=
    FiniteIntegralClosure.integralClosure_isDiscreteValuationRing_of_finite_separable K L base
  have hcC : IsAdicComplete (maximalIdeal C) C :=
    FiniteIntegralClosure.integralClosure_maximalIdeal_isAdicComplete_of_finite_separable K L base
  have : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eB.symm
  refine ⟨inferInstance, ?_⟩
  simpa only [IsLocalRing.map_ringEquiv_maximalIdeal] using
    (IsAdicComplete.congr_ringEquiv (maximalIdeal C) eB.symm).mpr hcC

private theorem faithfulSMul : FaithfulSMul R B := by
  apply (faithfulSMul_iff_algebraMap_injective R B).mpr
  intro x y h
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) L]
    exact (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R _)
  exact hRL (congrArg (fun z : B => (z : L)) h)

/-- The integral closure is faithfully flat over the DVR. -/
theorem faithfullyFlat : Module.FaithfullyFlat R B := by
  have := faithfulSMul R L
  exact Module.FaithfullyFlat.of_isIntegral_of_isDomain

/-- Over an algebraically closed residue field, the finite separable integral
closure induces an isomorphism on residue fields. -/
def residueEquiv [IsDiscreteValuationRing B] [IsAlgClosed (ResidueField R)]
    [FiniteDimensional (FractionRing R) L] [Algebra.IsSeparable (FractionRing R) L] :
    ResidueField R ≃+* ResidueField B := by
  have := faithfulSMul R L
  have : IsLocalHom (algebraMap R B) := (inferInstance : Algebra.IsIntegral R B).isLocalHom
  have : Module.Finite R B := IsIntegralClosure.finite R (FractionRing R) L B
  exact RingEquiv.ofBijective (algebraMap (ResidueField R) (ResidueField B))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

end Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension
