import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Int.WithZero
import Langlands.LocalField.ResidueNormalization

/-! # The actual X-adic Laurent-series local field -/

open scoped WithZero NNReal

universe u

namespace Langlands.LocalField.Laurent

variable (k : Type u) [Field k]

/-- The valuative relation of Mathlib's existing X-adic Laurent valuation. -/
@[instance_reducible]
noncomputable def valuativeRel : ValuativeRel (LaurentSeries k) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)

attribute [local instance] valuativeRel

instance valuationCompatible :
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

/-- This relation compares the existing X-adic valuation values. -/
theorem vle_iff (x y : LaurentSeries k) :
    x ≤ᵥ y ↔ (Valued.v x : ℤᵐ⁰) ≤ Valued.v y := Iff.rfl

/-- The topology already carried by Laurent series is the valuative topology. -/
instance isValuativeTopology : IsValuativeTopology (LaurentSeries k) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰) Valued.mem_nhds_zero

/-- Power series are precisely the integer ring of the existing X-adic valuation. -/
noncomputable def powerSeriesEquivValuedIntegers :
    PowerSeries k ≃+* (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer :=
  (LaurentSeries.powerSeriesEquivSubring k).trans (RingEquiv.subringCongr (by
    ext x
    simp only [LaurentSeries.powerSeries_as_subring, Subring.mem_map, Subring.mem_top,
      true_and, Valuation.mem_integer_iff]
    exact (LaurentSeries.val_le_one_iff_eq_coe k x).symm))

@[simp] theorem powerSeriesEquivValuedIntegers_coe (f : PowerSeries k) :
    ((powerSeriesEquivValuedIntegers k f :
      (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer) : LaurentSeries k) = f := rfl

/-- The actual residue field, identified by constant coefficient. -/
noncomputable def valuedResidueEquiv :
    IsLocalRing.ResidueField
      (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer ≃+* k :=
  (IsLocalRing.ResidueField.mapEquiv (powerSeriesEquivValuedIntegers k).symm).trans
    PowerSeries.residueFieldOfPowerSeries

@[simp] theorem valuedResidueEquiv_residue (f : PowerSeries k) :
    valuedResidueEquiv k (IsLocalRing.residue _ (powerSeriesEquivValuedIntegers k f)) =
      PowerSeries.constantCoeff f := by
  change PowerSeries.residueFieldOfPowerSeries
    (IsLocalRing.residue _ ((powerSeriesEquivValuedIntegers k).symm
      (powerSeriesEquivValuedIntegers k f))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

instance valuedIntegersDVR :
    IsDiscreteValuationRing (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (powerSeriesEquivValuedIntegers k)

/-- An explicit rank-one embedding for the X-adic valuation; the topology is unchanged. -/
@[instance_reducible]
noncomputable def valuationRankOne :
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).RankOne where
  hom' := (WithZeroMulInt.toNNReal (show (2 : ℝ≥0) ≠ 0 by norm_num)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := ⟨HahnSeries.single (1 : ℤ) (1 : k), by
    simp [LaurentSeries.valuation_single_zpow], by
    simp [LaurentSeries.valuation_single_zpow]⟩

attribute [local instance] valuationRankOne

instance nontrivialValuativeRel : ValuativeRel.IsNontrivial (LaurentSeries k) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)).mpr inferInstance

/-- The canonical valuation ring and the X-adic integer ring have the same elements. -/
theorem valuedIntegers_eq_ringOfIntegers :
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer =
      FML.ringOfIntegers (LaurentSeries k) := by
  ext x
  change Valued.v x ≤ (1 : ℤᵐ⁰) ↔ ValuativeRel.valuation (LaurentSeries k) x ≤ 1
  simpa only [map_one] using
    (ValuativeRel.isEquiv (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰)
      (ValuativeRel.valuation (LaurentSeries k))) x 1

/-- The comparison preserves the underlying Laurent-series element. -/
noncomputable def valuedIntegersEquivIntegers :
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer ≃+*
      FML.ringOfIntegers (LaurentSeries k) where
  toFun x := ⟨x, by rw [← valuedIntegers_eq_ringOfIntegers]; exact x.property⟩
  invFun x := ⟨x, by rw [valuedIntegers_eq_ringOfIntegers]; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Power series identify with the actual canonical valuation ring used by FML. -/
noncomputable def powerSeriesEquivIntegers :
    PowerSeries k ≃+* FML.ringOfIntegers (LaurentSeries k) :=
  (powerSeriesEquivValuedIntegers k).trans (valuedIntegersEquivIntegers k)

@[simp] theorem powerSeriesEquivIntegers_coe (f : PowerSeries k) :
    ((powerSeriesEquivIntegers k f :
      FML.ringOfIntegers (LaurentSeries k)) : LaurentSeries k) = f := rfl

/-- Reduction in the canonical valuation ring is actual constant coefficient. -/
noncomputable def residueEquiv :
    IsLocalRing.ResidueField (FML.ringOfIntegers (LaurentSeries k)) ≃+* k :=
  (IsLocalRing.ResidueField.mapEquiv (powerSeriesEquivIntegers k).symm).trans
    PowerSeries.residueFieldOfPowerSeries

private theorem powerSeriesResidueEquiv_residue
    {A : Type*} [CommRing A] [IsLocalRing A] (e : PowerSeries k ≃+* A)
    (f : PowerSeries k) :
    ((IsLocalRing.ResidueField.mapEquiv e.symm).trans
      PowerSeries.residueFieldOfPowerSeries) (IsLocalRing.residue A (e f)) =
      PowerSeries.constantCoeff f := by
  change PowerSeries.residueFieldOfPowerSeries
    (IsLocalRing.residue _ (e.symm (e f))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

@[simp] theorem residueEquiv_residue (f : PowerSeries k) :
    residueEquiv k (IsLocalRing.residue _ (powerSeriesEquivIntegers k f)) =
      PowerSeries.constantCoeff f :=
  powerSeriesResidueEquiv_residue k (powerSeriesEquivIntegers k) f

/-- Constant power series include the coefficient field in the actual integer ring. -/
noncomputable def coefficientInclusion : k →+* FML.ringOfIntegers (LaurentSeries k) :=
  (powerSeriesEquivIntegers k).toRingHom.comp PowerSeries.C

@[simp] theorem coefficientInclusion_coe (a : k) :
    ((coefficientInclusion k a : FML.ringOfIntegers (LaurentSeries k)) :
      LaurentSeries k) = (PowerSeries.C a : PowerSeries k) := rfl

@[simp] theorem residueEquiv_coefficientInclusion (a : k) :
    residueEquiv k (IsLocalRing.residue _ (coefficientInclusion k a)) = a := by
  change residueEquiv k (IsLocalRing.residue _ (powerSeriesEquivIntegers k
    (PowerSeries.C a))) = a
  rw [residueEquiv_residue, PowerSeries.constantCoeff_C]

variable [Finite k]

instance finiteValuedResidue : Finite (IsLocalRing.ResidueField
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).integer) :=
  Finite.of_equiv k (valuedResidueEquiv k).symm.toEquiv

open scoped Valued in
/-- Local compactness follows from pinned Laurent completeness, the actual DVR, and
its residue field, with no compactness or residue hypothesis beyond finiteness of `k`. -/
instance locallyCompactSpace : LocallyCompactSpace (LaurentSeries k) := by
  let := valuationRankOne k
  have : ProperSpace (LaurentSeries k) :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- Equal-characteristic local-field fixture for Mathlib's X-adic Laurent topology. -/
instance localField : IsNonarchimedeanLocalField (LaurentSeries k) where

@[simp] theorem residueCardinality_eq :
    LocalField.residueCardinality (LaurentSeries k) = Nat.card k :=
  Nat.card_congr (residueEquiv k).toEquiv

end Langlands.LocalField.Laurent
