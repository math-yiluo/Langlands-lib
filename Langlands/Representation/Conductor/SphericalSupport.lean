import Langlands.Representation.Conductor.Essential
import Langlands.Representation.Conductor.Congruence
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Langlands.Representation.Hecke.ActionIntegrand

/-! # General-field smooth root support for spherical coefficient integrands -/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa
open Langlands.Whittaker Langlands.HarmonicAnalysis Matrix Topology
open Langlands.Whittaker.UpperUnipotentCharacter

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]

/-- The actual closed valuation ball with radius the valuation of `ϖ^m`. -/
def uniformizerPowerLattice (ϖ : Fˣ) (m : ℤ) : Set F :=
  {x | ValuativeRel.valuation F x ≤ ValuativeRel.valuation F (ϖ : F) ^ m}

theorem uniformizerPowerLattice_mul_integer (ϖ : Fˣ) (m : ℤ) {y : F}
    (hy : y ∈ (ValuativeRel.valuation F).integer) :
    ((ϖ ^ m : Fˣ) : F) * y ∈ uniformizerPowerLattice ϖ m := by
  change ValuativeRel.valuation F (((ϖ ^ m : Fˣ) : F) * y) ≤ _
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀]
  change ValuativeRel.valuation F y ≤ 1 at hy
  exact mul_le_of_le_one_right zero_le hy

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

include hϖ in
/-- Uniformizer lattices are cofinal among the actual neighborhoods of zero. -/
theorem exists_uniformizerPowerLattice_subset {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ m : ℤ, uniformizerPowerLattice ϖ m ⊆ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).mp hs
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (γ : ValuativeRel.ValueGroupWithZero F)
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hx
    exact γ.ne_zero hx.symm
  obtain ⟨m, hm⟩ := hϖ.2 x hx0
  refine ⟨m + 1, fun t ht => hγ ?_⟩
  change ValuativeRel.valuation F t ≤ _ at ht
  change ValuativeRel.valuation F t < _
  apply ht.trans_lt
  rw [zpow_add₀ (valuation_pos (ValuativeRel.valuation F) ϖ).ne', zpow_one,
    ← hm, hx]
  exact mul_lt_of_lt_one_right (Units.zero_lt γ) hϖ.1

private theorem adjacentUnit_continuous {r : ℕ} (i : Fin r) :
    Continuous (fun t : F => (adjacentUnit i t).val) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro a <;> apply continuous_pi <;> intro b
  · change Continuous (fun t : F => transvection i.castSucc i.succ t a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · change Continuous (fun t : F => transvection i.castSucc i.succ (-t) a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem standardCharacter_adjacentUnit (ψ : UnitaryAdditiveCharacter F)
    {r : ℕ} (i : Fin r) (t : F) :
    (standardCharacter ψ r (adjacentUnit i t) : ℂ) = ψ.complex t := by
  rw [standardCharacter_apply]
  congr 1
  change (∑ j : Fin r, transvection i.castSucc i.succ t j.castSucc j.succ) = t
  have hentry (j : Fin r) :
      transvection i.castSucc i.succ t j.castSucc j.succ = if j = i then t else 0 := by
    simp [transvection, Matrix.single_apply, ne_of_lt j.castSucc_lt_succ, eq_comm]
  simp_rw [hentry]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem diagonalUnits_adjacentUnit {r : ℕ}
    (a : Fin (r + 1) → Fˣ) (i : Fin r) (t : F) :
    diagonalUnits a * (adjacentUnit i t).val =
      (adjacentUnit i (((a i.castSucc / a i.succ : Fˣ) : F) * t)).val *
        diagonalUnits a := by
  apply Units.ext
  change diagonal (fun j => (a j : F)) * transvection i.castSucc i.succ t =
    transvection i.castSucc i.succ (((a i.castSucc / a i.succ : Fˣ) : F) * t) *
      diagonal (fun j => (a j : F))
  ext j k
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Units.val_div_eq_div_val]
  by_cases hj : i.castSucc = j <;> by_cases hk : i.succ = k <;> by_cases hjk : j = k
    <;> simp_all [ne_of_lt i.castSucc_lt_succ, eq_comm]
  field_simp

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
variable (hπ : IsSmooth π)

include hϖ hπ in
/-- One uniformizer lattice fixes all root actions on the finite integral
orbit of a smooth vector. -/
theorem exists_uniformizerPowerLattice_fix_integral_orbit (v : V) :
    ∃ m : ℤ, ∀ t ∈ uniformizerPowerLattice ϖ m,
      ∀ κ ∈ integralSubgroup (ValuativeRel.valuation F).integer r,
        ∀ i : Fin r, π (adjacentUnit i t).val (π κ v) = π κ v := by
  let K := levelOpenSubgroup F r 0
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F)) :=
    isCompact_levelOpenSubgroup F r 0
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S := Set.range (fun k : K => π k.val v)
  have hS : S.Finite :=
    ((Langlands.Hecke.orbitMap_locallyConstant π (hπ v)).comp_continuous
      continuous_subtype_val).range_finite
  let : Finite S := hS.to_subtype
  let s : Set F := ⋂ i : Fin r, ⋂ w : S,
    {t | π (adjacentUnit i t).val w.val = w.val}
  have hs : IsOpen s := by
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro w
    exact ((Langlands.Hecke.orbitMap_locallyConstant π (hπ w.val)).comp_continuous
      (adjacentUnit_continuous i)) {w.val}
  have hzero : (0 : F) ∈ s := by
    simp only [s, Set.mem_iInter, Set.mem_ofPred_eq, adjacentUnit_zero,
      Subgroup.coe_one, map_one, Module.End.one_apply, implies_true]
  obtain ⟨m, hm⟩ := exists_uniformizerPowerLattice_subset hϖ (hs.mem_nhds hzero)
  refine ⟨m, fun t ht κ hκ i => ?_⟩
  have hκK : κ ∈ K := by
    change κ ∈ levelSubgroup F r 0
    rw [levelSubgroup_zero]
    exact hκ
  have hw : π κ v ∈ S := ⟨⟨κ, hκK⟩, rfl⟩
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (hm ht) i) ⟨π κ v, hw⟩

variable (ψ : UnitaryAdditiveCharacter F) (ℓ : glFunctionals ψ r π)

include hϖ hπ in
/-- Smooth Whittaker coefficients have a uniform integral bound on all
adjacent diagonal ratios, over every nonarchimedean local field. -/
theorem model_diagonal_root_integral_bound (hψ : HasIntegerConductor ψ)
    (f : (coefficientModel π ℓ).toSubmodule) :
    ∃ m : ℤ, ∀ (a : Fin (r + 1) → Fˣ)
      (κ : Langlands.GeneralLinear (r + 1) F),
      κ ∈ integralSubgroup (ValuativeRel.valuation F).integer r →
      f.val.val (diagonalUnits a * κ) ≠ 0 →
      ∀ i : Fin r, ((a i.castSucc / a i.succ : Fˣ) : F) *
        ((ϖ ^ m : Fˣ) : F) ∈ (ValuativeRel.valuation F).integer := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨m, hm⟩ := exists_uniformizerPowerLattice_fix_integral_orbit hϖ π hπ v
  refine ⟨m, fun a κ hκ hnonzero i => ?_⟩
  let c : F := ((a i.castSucc / a i.succ : Fˣ) : F)
  have hnonzero' : ℓ.val (π (diagonalUnits a * κ) v) ≠ 0 := hnonzero
  have hchar (t : F) (ht : t ∈ uniformizerPowerLattice ϖ m) :
      ψ.complex (c * t) = 1 := by
    have hfix := hm t ht κ hκ i
    have hact : π (adjacentUnit i (c * t)).val
        (π (diagonalUnits a * κ) v) = π (diagonalUnits a * κ) v := by
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc,
        ← diagonalUnits_adjacentUnit a i t, mul_assoc, map_mul, Module.End.mul_apply,
        map_mul, Module.End.mul_apply, hfix, map_mul, Module.End.mul_apply]
    have heq := ℓ.property (adjacentUnit i (c * t)) (π (diagonalUnits a * κ) v)
    rw [hact, standardCharacter_adjacentUnit] at heq
    exact mul_right_cancel₀ hnonzero' (heq.symm.trans (one_mul _).symm)
  apply hψ.2
  intro y hy
  apply Subtype.ext
  simpa only [c, mul_assoc, UnitaryAdditiveCharacter.complex_apply,
    Circle.coe_one] using
    hchar (((ϖ ^ m : Fˣ) : F) * y) (uniformizerPowerLattice_mul_integer ϖ m hy)

end Langlands.Conductor
