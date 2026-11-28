import Langlands.BruhatTits.IntegralModels.InducedTorusShallowCharacters
import Langlands.BruhatTits.IntegralModels.ConnectedImage.Integers
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Principal units and prime-to-characteristic torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalField Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "A" => sepClosureIntegers F
local notation "v" => sepClosureValuation F
local notation "ν" => algebraicExtensionAddValuation F Ω

theorem geometricValue_pos_iff (z : Ω) : (0 : WithTop ℝ) < ν z ↔ v z < 1 := by
  rw [lt_iff_not_ge, ← AddValuation.map_one ν]
  change ¬ logAdditiveValuation v (localLogScale F) (localLogScale_pos F) z ≤
    logAdditiveValuation v (localLogScale F) (localLogScale_pos F) 1 ↔ _
  rw [logAdditiveValuation_le_iff, map_one, not_le]

theorem eq_one_of_positiveDepth_of_pow
    (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) {r : ℝ≥0} (hr : 0 < r) {x : rationalPoints T.toGrp}
    (hx : x ∈ localGeometricCharacterCongruence F T r)
    {m : ℕ} (hm : IsUnit (m : A)) (hxm : x ^ m = 1) : x = 1 := by
  let L := localTorusSplittingData F T hT
  let y := rationalExtend K Ω T.toGrp x
  have hs := L.splits.baseChange_fieldTower K L.L Ω T.toGrp
  apply rationalExtend_injective_of_isAffine K Ω T.toGrp
  rw [map_one]
  apply eq_one_of_rationalCharacters_of_isSplitTorus
    ((CommGroupScheme.baseChange (baseMap K Ω)).obj T) hs y
  change x ∈ extendedCharacterCongruence K Ω ν T.toGrp r at hx
  rw [mem_extendedCharacterCongruence, mem_characterCongruence] at hx
  intro χ
  let z := rationalCharacterEval χ y
  have hz := (mem_addValuationUnitFiltration_of_pos ν hr z).mp (hx χ)
  have hr' : (0 : WithTop ℝ) < ((r : ℝ) : WithTop ℝ) := by exact_mod_cast hr
  have hlt : v ((z : Ω) - 1) < 1 := (geometricValue_pos_iff F _).mp (hr'.trans_le hz)
  have hz₁ : v (z : Ω) = 1 := by
    calc
      v (z : Ω) = v (1 + ((z : Ω) - 1)) := congrArg v (by ring)
      _ = 1 := (v).map_one_add_of_lt hlt
  let a : A := ⟨(z : Ω), hz₁.le⟩
  have hma : a ^ m = 1 := by
    have hh := congrArg ((rationalCharacterEval χ).comp (rationalExtend K Ω T.toGrp)) hxm
    rw [map_pow, map_one] at hh
    exact Subtype.ext (congrArg Units.val hh)
  have haMem : a - 1 ∈ maximalIdeal A := (mem_maximalIdeal_iff_lt v _).mpr hlt
  have ha := eq_of_pow_eq_one_of_sub_mem hm hma (one_pow m) haMem
  exact Units.ext (congrArg Subtype.val ha)

private local instance baseNormed : NontriviallyNormedField F := localNormedField F
private local instance baseUltra : IsUltrametricDist F := localNormedField_ultrametric F
private local instance baseComplete : CompleteSpace F := localNormedField_complete F
private local instance baseResidueFinite : Finite (ResidueField (baseIntegers F)) :=
  localResidue_finite F

local notation "AΩ" => extensionIntegers F Ω

private theorem exists_teich_lift (x : AΩ) (hx : residue AΩ x ≠ 0) :
    ∃ (m : ℕ) (t : AΩ), m ≠ 0 ∧ (t : Ω) ∈ K ∧ t ^ m = 1 ∧ IsUnit (m : AΩ) ∧
      residue AΩ t = residue AΩ x := by
  obtain ⟨d, hd, hxpow⟩ := exists_pow_card_pow_sub_one_eq_one
    (Algebra.IsIntegral.isIntegral (R := ResidueField (baseIntegers F)) (residue AΩ x)) hx
  let m := Nat.card (ResidueField (baseIntegers F)) ^ d - 1
  let : NeZero m := ⟨teichOrder_ne_zero F hd⟩
  obtain ⟨ζ, hζ⟩ := exists_teich F hd
  obtain ⟨n, _, hn⟩ := (isPrimitiveRoot_residue F hd hζ).eq_pow_of_pow_eq_one hxpow
  have ht : (ζ ^ n) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨m, ζ ^ n, NeZero.ne m, mem_inertiaFixedField_of_pow_eq_one F hd _ ht, ht,
    teichOrder_isUnit F hd, ?_⟩
  rw [map_pow, hn]

private theorem exists_units_factor {R k : Type u} [CommRing R] [Field k]
    (f : R →+* k) (w : Rˣ) (z : R) {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1)
    (h : f z = f (w : R)) :
    ∃ b t : Rˣ, w = b * t ∧ t ^ m = 1 ∧ f (b : R) = 1 := by
  let hu : IsUnit z := IsUnit.of_pow_eq_one hz hm
  let t := hu.unit
  let b := w * t⁻¹
  have ht : (t : R) = z := hu.unit_spec
  have htPow : t ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ht, hz, Units.val_one])
  refine ⟨b, t, (inv_mul_cancel_right w t).symm, htPow, ?_⟩
  let g := Units.map f.toMonoidHom
  have he : g w = g t := Units.ext (by change f (w : R) = f (t : R); rw [ht, h])
  exact congrArg Units.val (show g b = 1 by rw [show b = w * t⁻¹ from rfl, map_mul,
    map_inv, he, mul_inv_cancel])

variable (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))

local notation "Oₗ" => Langlands.BruhatTits.IntegralModels.ConnectedImage.integers F L

private def toSepIntegers : Oₗ →+* AΩ where
  toFun x := ⟨((x : L) : Ω), x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem toSepIntegers_injective : Function.Injective (toSepIntegers F L) :=
  fun _ _ h => Subtype.ext
    ((algebraMap L Ω).injective (congrArg (fun c : AΩ => (c : Ω)) h))

private theorem exists_preimage_of_mem_base (τ : AΩ) (hτ : (τ : Ω) ∈ K) :
    ∃ z : Oₗ, toSepIntegers F L z = τ := by
  let z : Oₗ := ⟨algebraMap K L (⟨(τ : Ω), hτ⟩ : K), τ.property⟩
  exact ⟨z, rfl⟩

private theorem unit_separable_of_unit_extension (m : ℕ) (hm : IsUnit (m : AΩ)) :
    IsUnit (m : A) := by
  let e : AΩ ≃+* A := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (sepClosureIntegers_eq F).symm)
  rw [← map_natCast e]
  exact hm.map e

private theorem value_sub_one_lt_one_of_residue_eq_one {L : Type u} [Field L]
    (w : Valuation L ℝ≥0) (z : w.valuationSubring)
    (hz : residue w.valuationSubring z = 1) : w ((z : L) - 1) < 1 := by
  have h : z - 1 ∈ maximalIdeal w.valuationSubring := by
    rw [← residue_eq_zero_iff, map_sub, hz, map_one, sub_self]
  exact (mem_maximalIdeal_iff_lt w _).mp h

private theorem principal_of_residue_eq_one (z : AΩ) (hz : residue AΩ z = 1) :
    (0 : WithTop ℝ) < ν ((z : Ω) - 1) :=
  (geometricValue_pos_iff F _).mpr
    (value_sub_one_lt_one_of_residue_eq_one (spectralValuation F Ω) z hz)

set_option maxHeartbeats 2600000 in
/-- A coefficient unit over an intermediate field has a principal part
and a torsion part whose order is a unit in the separable valuation ring. -/
theorem exists_principal_and_torsion (w : Oₗˣ) :
    ∃ (b t : Oₗˣ) (m : ℕ), w = b * t ∧ t ^ m = 1 ∧ IsUnit (m : A) ∧
      (0 : WithTop ℝ) < ν (((b : Oₗ) : L) - 1 : Ω) := by
  let i := toSepIntegers F L
  let x := i (w : Oₗ)
  let f := (residue AΩ).comp i
  have hx : residue AΩ x ≠ 0 := (w.isUnit.map f).ne_zero
  obtain ⟨m, τ, hm₀, hτK, hτ, hm, hτred⟩ := exists_teich_lift F x hx
  obtain ⟨z, hz⟩ := exists_preimage_of_mem_base F L τ hτK
  have hi : Function.Injective i := toSepIntegers_injective F L
  have hzpow : z ^ m = 1 := hi (by rw [map_pow, show i z = τ from hz, hτ, map_one])
  have hzred : f z = f (w : Oₗ) :=
    (congrArg (residue AΩ) hz).trans hτred
  obtain ⟨b, t, hw, ht, hb⟩ := exists_units_factor f w z hm₀ hzpow hzred
  exact ⟨b, t, m, hw, ht, unit_separable_of_unit_extension F m hm,
    principal_of_residue_eq_one F (i (b : Oₗ)) hb⟩

end Langlands.Geometry.Building
