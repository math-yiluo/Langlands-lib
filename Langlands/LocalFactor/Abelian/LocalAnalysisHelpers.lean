import Langlands.LocalFactor.PadicAbelianStatement
import Langlands.LocalFactor.Abelian.Laurent
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Topology.LocallyProfiniteProof
import Langlands.LocalField.Topology

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- The kernel of a continuous local-field quasicharacter is open. -/
theorem quasicharacter_open_kernel (χ : Character) :
    letI := T.topology
    IsOpen {v : F.Carrierˣ | χ v = 1} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  let : TotallyDisconnectedSpace F.Carrierˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : NonarchimedeanGroup F.Carrierˣ := by
    refine ⟨?_⟩
    intro U hU
    obtain ⟨H, _, hH⟩ :=
      ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
        Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
    exact ⟨H, hH⟩
  exact Langlands.isOpen_ker_of_continuous_complex_character χ.toMonoidHom χ.continuous

/-- Quasicharacters take locally constant values in the complex unit group. -/
theorem quasicharacter_locallyConstant (χ : Character) :
    letI := T.topology
    IsLocallyConstant (fun v : F.Carrierˣ => χ v) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro u
  refine ⟨(fun v : F.Carrierˣ => u⁻¹ * v) ⁻¹' {v | χ v = 1},
    (quasicharacter_open_kernel T χ).preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro v hv
    have he : (χ u)⁻¹ * χ v = 1 := by simpa using hv
    exact (inv_mul_eq_one.mp he).symm

/-- At level zero the quasicharacter has absolute value one. -/
theorem quasicharacter_norm_units (χ : Character) (v : F.Carrierˣ)
    (hv : unitLevel T 0 v) : ‖(χ v : ℂ)‖ = 1 := by
  let := T.topology
  apply T.norm_eq_one_of_normalizedAbs_eq_one χ.toMonoidHom
    (quasicharacter_open_kernel T χ)
  have ho : T.ord (v : F.Carrier) = 0 := by simpa [unitLevel] using hv
  simp [T.normalizedAbs_of_ne_zero v.ne_zero, ho]

/-- The image of the actual integral unit group is finite. -/
theorem quasicharacter_finite_unit_image (χ : Character) :
    (Set.range (fun v : {v : F.Carrierˣ // unitLevel T 0 v} => χ v.val)).Finite := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hset : {v : F.Carrierˣ | unitLevel T 0 v} =
      {v : F.Carrierˣ | T.normalizedAbs (v : F.Carrier) = 1} := by
    ext v
    change unitLevel T 0 v ↔ T.normalizedAbs (v : F.Carrier) = 1
    rw [unitLevel_iff_mem_principalUnits, T.mem_principalUnits_zero,
      T.normalizedAbs_eq_one_iff_valuation_eq_one]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier v.val) = 1 ↔ _
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective.eq_iff
  have hcompact : IsCompact {v : F.Carrierˣ | unitLevel T 0 v} := by
    rw [hset]
    exact T.isCompact_normalizedAbs_eq_one_units
  let : CompactSpace {v : F.Carrierˣ // unitLevel T 0 v} :=
    isCompact_iff_compactSpace.mp hcompact
  exact ((quasicharacter_locallyConstant T χ).comp_continuous continuous_subtype_val).range_finite

/-- The explicit least-level conductor exists uniquely. -/
theorem existsUnique_conductorAt (χ : Character) : ∃! a : ℕ, ConductorAt T χ a := by
  refine ⟨T.multiplicativeConductor χ, (conductorAt_iff T χ _).mpr rfl, ?_⟩
  intro a ha
  exact (conductorAt_iff T χ a).mp ha

/-- Character inversion preserves the exact conductor. -/
theorem conductorAt_inv (χ : Character) (a : ℕ) (ha : ConductorAt T χ a) :
    ConductorAt T χ⁻¹ a := by
  have he (k : ℕ) :
      (∀ v : F.Carrierˣ, unitLevel T k v → χ⁻¹ v = 1) ↔
      (∀ v : F.Carrierˣ, unitLevel T k v → χ v = 1) := by
    change (∀ v : F.Carrierˣ, unitLevel T k v → (χ v)⁻¹ = 1) ↔ _
    simp only [inv_eq_one]
  exact ⟨(he a).mpr ha.1, fun k hk => ha.2 ((he k).mp hk)⟩

/-- The conductor of a product is bounded above by the maximum. -/
theorem conductorAt_mul_le (χ η : Character) (a b : ℕ)
    (ha : ConductorAt T χ a) (hb : ConductorAt T η b) :
    ∃ c : ℕ, ConductorAt T (χ * η) c ∧ c ≤ max a b := by
  obtain ⟨c, hc, _⟩ := existsUnique_conductorAt T (χ * η)
  refine ⟨c, hc, hc.2 ?_⟩
  intro v hv
  have hav : unitLevel T a v := (unitLevel_iff_mem_principalUnits T a v).mpr
    (T.principalUnits_antitone (le_max_left a b)
      ((unitLevel_iff_mem_principalUnits T _ v).mp hv))
  have hbv : unitLevel T b v := (unitLevel_iff_mem_principalUnits T b v).mpr
    (T.principalUnits_antitone (le_max_right a b)
      ((unitLevel_iff_mem_principalUnits T _ v).mp hv))
  simp [ha.1 v hav, hb.1 v hbv]

/-- Unequal conductors give equality in the maximum bound. -/
theorem conductorAt_mul_of_ne (χ η : Character) (a b : ℕ)
    (ha : ConductorAt T χ a) (hb : ConductorAt T η b) (hab : a ≠ b) :
    ConductorAt T (χ * η) (max a b) := by
  obtain ⟨c, hc, hcab⟩ := conductorAt_mul_le T χ η a b ha hb
  obtain ⟨d, hd, hdc⟩ := conductorAt_mul_le T (χ * η) η⁻¹ c b hc (conductorAt_inv T η b hb)
  have hdχ : ConductorAt T χ d := by simpa using hd
  have had : a = d := ha.unique hdχ
  obtain ⟨e, he, hec⟩ := conductorAt_mul_le T χ⁻¹ (χ * η) a c (conductorAt_inv T χ a ha) hc
  have heη : ConductorAt T η e := by simpa [mul_assoc] using he
  have hbe : b = e := hb.unique heη
  have heq : c = max a b := by omega
  exact heq ▸ hc

/-- An unramified twist preserves the conductor, including conductor zero. -/
theorem conductorAt_mul_unramified (χ η : Character) (a : ℕ)
    (ha : ConductorAt T χ a) (hb : ConductorAt T η 0) :
    ConductorAt T (χ * η) a := by
  by_cases h : a = 0
  · subst a
    obtain ⟨c, hc, hle⟩ := conductorAt_mul_le T χ η 0 0 ha hb
    have hc0 : c = 0 := by simpa using hle
    exact hc0 ▸ hc
  · simpa using conductorAt_mul_of_ne T χ η a 0 ha hb h

end Langlands.LocalFactor.PadicAbelian
