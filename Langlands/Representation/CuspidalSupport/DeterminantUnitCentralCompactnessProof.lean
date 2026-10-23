import Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement

/-! Compactness of the determinant-unit subgroup's intersection with the Levi center. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF

/-- The norm-one units of the field are compact for the supplied topology. -/
theorem isCompact_ker_normalizedAbsUnits
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    IsCompact (T.normalizedAbsUnits.ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let S : Set F.Carrier := {x | ValuativeRel.valuation F.Carrier x = 1}
  have hS : IsCompact S := by
    have hcl : IsClosed S := by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation F.Carrier).isClosed_sphere (r := 1)
    exact (IsNonarchimedeanLocalField.isCompact_closedBall F.Carrier 1).of_isClosed_subset hcl
      fun x hx => le_of_eq hx
  have he : (T.normalizedAbsUnits.ker : Set F.Carrierˣ) = Units.val ⁻¹' S := by
    ext a
    change a ∈ T.normalizedAbsUnits.ker ↔ ValuativeRel.valuation F.Carrier (a : F.Carrier) = 1
    rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
    change T.normalizedAbs a = 1 ↔ _
    rw [T.normalizedAbs_eq_one_iff_discreteValuation]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier (a : F.Carrier)) = 1 ↔ _
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective.eq_iff
  rw [he]
  refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS fun x hx => ?_
  have hx0 : x ≠ 0 := by
    intro h
    have hx' : ValuativeRel.valuation F.Carrier x = 1 := hx
    rw [h, map_zero] at hx'
    exact zero_ne_one hx'
  exact ⟨Units.mk0 x hx0, rfl⟩

/-- BZ76 §3.20(a): the blockwise determinant-unit subgroup meets the actual
Levi center in a compact set. -/
theorem leviDeterminantUnitCentralCompactness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviDeterminantUnitCentralCompactnessTheorem F T B := by
  let := T.topology
  let Φ : (Fin B.length → F.Carrierˣ) → B.Levi F.Carrier := fun c i => scalar (c i)
  have hΦ : Continuous Φ := continuous_pi fun i =>
    (GeneralLinear.scalarContinuous (n := B.size i)).continuous.comp (continuous_apply i)
  have heq : (((determinantUnitSubgroup T B) ⊓ Subgroup.center (B.Levi F.Carrier) :
      Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier)) =
      Φ '' Set.univ.pi fun _ => (T.normalizedAbsUnits.ker : Set F.Carrierˣ) := by
    ext g
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      mem_determinantUnitSubgroup, Subgroup.center_pi, Subgroup.mem_pi, Set.mem_univ,
      true_implies, Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
      Set.mem_image, Set.mem_pi, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hdet, hcen⟩
      choose c hc using hcen
      refine ⟨c, fun i => ?_, funext hc⟩
      have h := hdet i
      rw [← hc i, T.determinantNorm_scalar, ← Units.val_inj, Units.val_pow_eq_pow_val,
        Units.val_one, pow_eq_one_iff_of_nonneg zero_le (B.positive i).ne'] at h
      exact Units.val_inj.mp h
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => ?_, fun i => ⟨c i, rfl⟩⟩
      change T.determinantNorm (B.size i) (scalar (c i)) = 1
      rw [T.determinantNorm_scalar, hc i, one_pow]
  change IsCompact (((determinantUnitSubgroup T B) ⊓ Subgroup.center (B.Levi F.Carrier) :
      Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_ker_normalizedAbsUnits T).image hΦ

end Langlands.CuspidalSupport
