import Langlands.Geometry.FormalGroup.DrinfeldCoefficientLift
import Langlands.Geometry.FormalGroup.DrinfeldIntegralCyclicRelations
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalRing

/-! # The cyclic characters of the unramified integer subfield -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision
open scoped TensorProduct

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

/-- The integral rank agrees with the degree of the given unramified subfield. -/
theorem subfieldInteger_finrank (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    Module.finrank 𝒪[K] (SubfieldIntegerRing K D ι) = CentralSimple.reducedDegree K D := by
  let C := SubfieldIntegerRing K D ι
  let : Algebra 𝒪[K] L := Algebra.compHom L (algebraMap 𝒪[K] K)
  let : IsScalarTower 𝒪[K] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower 𝒪[K] C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsFractionRing C L := (Valuation.integer.integers
    (localDivisionSubfieldValuation K D ι)).isFractionRing
  exact (IsFractionRing.finrank_eq 𝒪[K] K C L).symm.trans hL.2.2.2

/-- The actual residue field of the unramified integer subfield has degree d. -/
theorem subfieldResidue_finrank (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    Module.finrank 𝓀[K] (IsLocalRing.ResidueField (SubfieldIntegerRing K D ι)) =
      CentralSimple.reducedDegree K D := by
  let C := SubfieldIntegerRing K D ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  let : Module.Free 𝒪[K] C := Module.free_of_flat_of_isLocalRing
  have hm : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] C) =
      IsLocalRing.maximalIdeal C := Algebra.FormallyUnramified.map_maximalIdeal
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (IsLocalRing.maximalIdeal 𝒪[K])
  let e' : IsLocalRing.ResidueField C ≃ₐ[𝓀[K]] (𝓀[K] ⊗[𝒪[K]] C) :=
    { __ := (Ideal.quotEquivOfEq hm.symm).trans e.toRingEquiv
      commutes' := by
        intro t
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
        rw [IsLocalRing.ResidueField.algebraMap_residue]
        change e (Ideal.quotEquivOfEq hm.symm (Ideal.Quotient.mk _ (algebraMap 𝒪[K] C a))) = _
        rw [Ideal.quotEquivOfEq_mk]
        change Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (IsLocalRing.maximalIdeal 𝒪[K])
          (Ideal.Quotient.mk _ (algebraMap 𝒪[K] C a)) = _
        rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
          ← Algebra.TensorProduct.algebraMap_apply']
        rfl }
  calc
    Module.finrank 𝓀[K] (IsLocalRing.ResidueField C) =
        Module.finrank 𝓀[K] (𝓀[K] ⊗[𝒪[K]] C) := e'.toLinearEquiv.finrank_eq
    _ = Module.finrank 𝒪[K] C := Module.finrank_baseChange
    _ = CentralSimple.reducedDegree K D := subfieldInteger_finrank ι hL

variable (σ : L ≃ₐ[K] L)

/-- The valuation condition in the cyclic relations gives arithmetic Frobenius after reduction. -/
theorem subfieldIntegerFrobenius_residue_pow
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hσ : ∀ a : SubfieldIntegerRing K D ι,
      localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
    (a : SubfieldIntegerRing K D ι) :
    IsLocalRing.residue _ (subfieldIntegerFrobenius ι σ hL a) =
      (IsLocalRing.residue _ a) ^ Nat.card 𝓀[K] := by
  let t := subfieldIntegerFrobenius ι σ hL a - a ^ Nat.card 𝓀[K]
  have hv : localDivisionSubfieldValuation K D ι (t : L) < 1 := by
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    apply e.toOrderIso.lt_iff_lt.mp
    change e (localReducedNormValuation K D (ι (t : L))) < e 1
    rw [map_one]
    change localReducedNormIntValuation K D (ι (t : L)) < 1
    change localReducedNormIntValuation K D
      (ι ((subfieldIntegerFrobenius ι σ hL a : L) - (a : L) ^ Nat.card 𝓀[K])) < 1
    rw [map_sub, subfieldIntegerFrobenius_coe]
    exact hσ a
  have hr : IsLocalRing.residue _ t = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact fun hu => hv.ne ((DivisionValuation.isUnit_iff_value_eq_one _ t).mp hu)
  exact sub_eq_zero.mp (by simpa only [t, map_sub, map_pow] using hr)

/-- Arithmetic Frobenius on the residue field of the actual integer subfield. -/
def subfieldResidueFrobenius (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) ≃ₐ[𝓀[K]]
      IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) := by
  let C := SubfieldIntegerRing K D ι
  letI : Module.Finite 𝒪[K] C := hL.2.1
  letI : Finite (IsLocalRing.ResidueField C) := IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪[K]) (S := C) inferInstance
  letI := Fintype.ofFinite 𝓀[K]
  exact FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] (IsLocalRing.ResidueField C)

@[simp]
theorem subfieldResidueFrobenius_apply (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (a : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι)) :
    subfieldResidueFrobenius ι hL a = a ^ Nat.card 𝓀[K] := by
  unfold subfieldResidueFrobenius
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]

/-- The cycle length of residue Frobenius is the reduced degree. -/
theorem subfieldResidueFrobenius_orderOf (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    orderOf (subfieldResidueFrobenius ι hL) = CentralSimple.reducedDegree K D := by
  let C := SubfieldIntegerRing K D ι
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite (IsLocalRing.ResidueField C) := IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪[K]) (S := C) inferInstance
  let := Fintype.ofFinite 𝓀[K]
  exact (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic 𝓀[K]
    (IsLocalRing.ResidueField C)).trans (subfieldResidue_finrank ι hL)

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]

/-- Order the residue characters by the inverse arithmetic Frobenius orbit of an embedding. -/
def subfieldCyclicCharacter (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (i : Fin (CentralSimple.reducedDegree K D)) : SubfieldIntegerRing K D ι →ₐ[𝒪[K]] κ :=
  ((j.comp ((subfieldResidueFrobenius ι hL)⁻¹ ^ i.val).toAlgHom).restrictScalars 𝒪[K]).comp
    (IsScalarTower.toAlgHom 𝒪[K] (SubfieldIntegerRing K D ι) _)

/-- The first d inverse Frobenius powers give distinct characters. -/
theorem subfieldCyclicCharacter_injective (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ) :
    Function.Injective (subfieldCyclicCharacter ι hL j) := by
  let f := (subfieldResidueFrobenius ι hL)⁻¹
  have horder : orderOf f = CentralSimple.reducedDegree K D :=
    (orderOf_inv _).trans (subfieldResidueFrobenius_orderOf ι hL)
  intro i i' h
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := f)
  · exact horder.symm ▸ i.isLt
  · exact horder.symm ▸ i'.isLt
  ext t
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
  apply j.injective
  exact AlgHom.congr_fun h a

/-- Moving one step in the cycle precomposes the character with inverse integral Frobenius. -/
theorem subfieldCyclicCharacter_succ (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    [NeZero (CentralSimple.reducedDegree K D)]
    (hσ : ∀ a : SubfieldIntegerRing K D ι,
      localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (i : Fin (CentralSimple.reducedDegree K D)) (a : SubfieldIntegerRing K D ι) :
    subfieldCyclicCharacter ι hL j (i + 1) a =
      subfieldCyclicCharacter ι hL j i ((subfieldIntegerFrobenius ι σ hL).symm a) := by
  let f := subfieldResidueFrobenius ι hL
  let s := subfieldIntegerFrobenius ι σ hL
  let r := IsLocalRing.residue (SubfieldIntegerRing K D ι)
  have hinv : f.symm (r a) = r (s.symm a) := by
    apply f.injective
    rw [f.apply_symm_apply]
    have h := subfieldIntegerFrobenius_residue_pow ι σ hL hσ (s.symm a)
    change r (s (s.symm a)) = (r (s.symm a)) ^ Nat.card 𝓀[K] at h
    rw [s.apply_symm_apply] at h
    rw [show f (r (s.symm a)) = (r (s.symm a)) ^ Nat.card 𝓀[K]
      from subfieldResidueFrobenius_apply ι hL _]
    exact h
  have horder : orderOf f⁻¹ = CentralSimple.reducedDegree K D :=
    (orderOf_inv _).trans (subfieldResidueFrobenius_orderOf ι hL)
  have hidx : (i + 1).val = (i.val + 1) % CentralSimple.reducedDegree K D := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hpow : f⁻¹ ^ (i + 1).val = f⁻¹ ^ (i.val + 1) :=
    (congrArg (f⁻¹ ^ ·) (hidx.trans (congrArg ((i.val + 1) % ·) horder.symm))).trans
      (pow_mod_orderOf _ _)
  change j ((f⁻¹ ^ (i + 1).val) (r a)) = j ((f⁻¹ ^ i.val) (r (s.symm a)))
  rw [hpow, pow_succ]
  change j ((f⁻¹ ^ i.val) (f.symm (r a))) = j ((f⁻¹ ^ i.val) (r (s.symm a)))
  rw [hinv]

variable {ι} {π : 𝒪[K]} {B : Nilp.{u, v} 𝒪[K] π}

/-- Distinct cyclic characters have lifts separated by a unit on any residue coordinate. -/
theorem subfieldCyclicCharacter_lifts_separated
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
    {i i' : Fin (CentralSimple.reducedDegree K D)} (hii' : i ≠ i') :
    ∃ a : SubfieldIntegerRing K D ι,
      IsUnit (subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ a -
        subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i') ψ a) := by
  let χ := subfieldCyclicCharacter ι hL j
  have hh : χ i ≠ χ i' := fun h => hii' (subfieldCyclicCharacter_injective ι hL j h)
  obtain ⟨a, ha⟩ : ∃ a, χ i a ≠ χ i' a := by
    by_contra! h
    exact hh (AlgHom.ext h)
  refine ⟨a, (Nilp.reductionIdeal_isNilpotent B).isUnit_quotient_mk_iff.mp ?_⟩
  change IsUnit (Nilp.reductionQuotient π B.obj
    (subfieldCoefficientLift hL (χ i) ψ a - subfieldCoefficientLift hL (χ i') ψ a))
  rw [map_sub]
  have hi : Nilp.reductionQuotient π B.obj (subfieldCoefficientLift hL (χ i) ψ a) =
      ψ (χ i a) := AlgHom.congr_fun (reductionQuotient_comp_subfieldCoefficientLift hL (χ i) ψ) a
  have hi' : Nilp.reductionQuotient π B.obj (subfieldCoefficientLift hL (χ i') ψ a) =
      ψ (χ i' a) := AlgHom.congr_fun (reductionQuotient_comp_subfieldCoefficientLift hL (χ i') ψ) a
  rw [hi, hi', ← map_sub]
  exact (sub_ne_zero.mpr ha).isUnit.map ψ

end Langlands.FormalGroup.LocalDivision
