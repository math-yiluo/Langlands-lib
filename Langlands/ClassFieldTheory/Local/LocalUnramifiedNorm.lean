import Langlands.ClassFieldTheory.Local.LocalFieldIntegerExtension
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.LocalClassField.UnramifiedAlgebraProof
import Langlands.Representation.Plancherel.TorusNormKernel.FieldNormCompact
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Valuation.Integral

noncomputable section

open IsLocalRing ValuativeRel Langlands.LocalClassField
open scoped nonZeroDivisors

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Inclusion of the actual integer units in the field units. -/
def localIntegerUnitsInclusion : (𝒪[K])ˣ →* Kˣ :=
  Units.map (algebraMap (𝒪[K]) K)

theorem localIntegerUnitsInclusion_order (x : (𝒪[K])ˣ) :
    normalizedUnitOrder K (.ofMul (localIntegerUnitsInclusion K x)) = 0 :=
  (normalizedUnitOrder_eq_zero_iff K _).mpr
    ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp x.isUnit)

theorem exists_localIntegerUnitsInclusion (a : Kˣ)
    (ha : normalizedUnitOrder K (.ofMul a) = 0) :
    ∃ x : (𝒪[K])ˣ, localIntegerUnitsInclusion K x = a := by
  have ha' := (normalizedUnitOrder_eq_zero_iff K a).mp ha
  let x : 𝒪[K] := ⟨a, ha'.le⟩
  obtain ⟨y, hy⟩ := (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr
    (show valuation K (algebraMap (𝒪[K]) K x) = 1 from ha')
  exact ⟨y, Units.ext (congrArg Subtype.val hy)⟩

variable (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

/-- The supplied upper valuation ring is the integral closure in the finite extension. -/
theorem localIntegerAlgebra_isIntegralClosure (hcont : Continuous (algebraMap K L)) :
    IsIntegralClosure (𝒪[L]) (𝒪[K]) L := by
  let := localIntegerAlgebra_finite K L hcont
  refine ⟨Subtype.val_injective, fun {x} => ?_⟩
  constructor
  · intro hx
    have hx' : IsIntegral (𝒪[L]) x := hx.tower_top
    exact ⟨⟨x, (Valuation.integer.integers (valuation L)).isIntegral_iff_v_le_one.mp hx'⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact (IsIntegral.of_finite (R := (𝒪[K])) x).algebraMap

/-- The determinant norm of an integer is the integral value of its field norm. -/
theorem localIntegerNorm_eq_fieldNorm (hcont : Continuous (algebraMap K L)) (x : 𝒪[L]) :
    Algebra.norm K (x : L) = (Algebra.norm (𝒪[K]) x : K) := by
  let := localIntegerAlgebra_finite K L hcont
  let := localIntegerAlgebra_isIntegralClosure K L hcont
  let : IsFractionRing (𝒪[K]) K := (Valuation.integer.integers (valuation K)).isFractionRing
  let := IsIntegralClosure.isLocalization (𝒪[K]) K L (𝒪[L])
  exact Algebra.norm_localization (𝒪[K]) ((𝒪[K])⁰) x

/-- The determinant norm on the integer unit groups. -/
def localIntegerNorm : (𝒪[L])ˣ →* (𝒪[K])ˣ :=
  Units.map (Algebra.norm (𝒪[K]))

theorem normUnits_localIntegerUnitsInclusion (hcont : Continuous (algebraMap K L))
    (x : (𝒪[L])ˣ) :
    normUnits K L (localIntegerUnitsInclusion L x) =
      localIntegerUnitsInclusion K (localIntegerNorm K L x) :=
  Units.ext (localIntegerNorm_eq_fieldNorm K L hcont x)

private theorem continuous_localIntegerNorm (hcont : Continuous (algebraMap K L)) :
    Continuous (localIntegerNorm K L) := by
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField L
  let := LocalGalois.localNormedField_complete K
  let : ContinuousSMul K L := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  let : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional
  have h : Continuous (Algebra.norm (𝒪[K]) : (𝒪[L]) → (𝒪[K])) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : 𝒪[L] => (Algebra.norm (𝒪[K]) x : K))
    simp_rw [← localIntegerNorm_eq_fieldNorm K L hcont]
    exact (Langlands.Plancherel.TorusNormKernel.continuous_algebraNorm (F := K) (E := L)).comp
      continuous_subtype_val
  exact Units.continuous_iff.mpr
    ⟨h.comp Units.continuous_val, h.comp Units.continuous_coe_inv⟩

/-- For an unramified extension the determinant norm is onto the integer units. -/
theorem localIntegerNorm_surjective (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) :
    Function.Surjective (localIntegerNorm K L) := by
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField L
  let := localIntegerAlgebra_finite K L hcont
  have hI : Ideal.map (algebraMap (𝒪[K]) (𝒪[L])) (𝓂[K]) = 𝓂[L] := by
    rw [map_maximalIdeal_eq_localRamificationFactor, he, pow_one]
  obtain ⟨_, happrox⟩ := UnramifiedAlgebra.proof (𝒪[K]) (𝒪[L]) hI
  intro y
  let N := localIntegerNorm K L
  let C (n : ℕ) : Set (𝒪[L])ˣ :=
    {x | ((y * (N x)⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n}
  have hC_nonempty (n : ℕ) : (C n).Nonempty := by
    induction n with
    | zero => exact ⟨1, by simp [C]⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨z, _, hz⟩ := happrox n (y * (N x)⁻¹) hx
      refine ⟨x * z, ?_⟩
      change ((y * (N (x * z))⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) - 1 ∈ 𝓂[K] ^ (n + 1)
      simpa only [N, localIntegerNorm, map_mul, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
        using hz
  have hC_step (n : ℕ) : C (n + 1) ⊆ C n :=
    fun _ hx => Ideal.pow_le_pow_right n.le_succ hx
  have hC_closed (n : ℕ) : IsClosed (C n) :=
    (IsNoetherianRing.isClosed_ideal ((𝓂[K]) ^ n)).preimage
      ((Units.continuous_val.comp (continuous_const.mul
        (continuous_localIntegerNorm K L hcont).inv)).sub continuous_const)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hC_step hC_nonempty (hC_closed 0).isCompact hC_closed
  have h : ((y * (N x)⁻¹ : (𝒪[K])ˣ) : 𝒪[K]) - 1 ∈ ⨅ n : ℕ, 𝓂[K] ^ n :=
    (Submodule.mem_iInf _).mpr fun n => (Set.mem_iInter.mp hx n : x ∈ C n)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at h
  exact ⟨x, (mul_inv_eq_one.mp (Units.ext (sub_eq_zero.mp h))).symm⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem normUnits_base (a : Kˣ) :
    normUnits K L (Units.map (algebraMap K L) a) = a ^ Module.finrank K L := by
  apply Units.ext
  exact Algebra.norm_algebraMap (S := L) (a : K)

/-- The field norm in an unramified extension multiplies normalized order by the degree. -/
theorem normalizedUnitOrder_norm_of_unramified (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) (b : Lˣ) :
    normalizedUnitOrder K (.ofMul (normUnits K L b)) =
      (Module.finrank K L : ℤ) * normalizedUnitOrder L (.ofMul b) := by
  let z := normalizedUnitOrder L (.ofMul b)
  let p : Lˣ := Units.map (algebraMap K L) (localUniformizer K)
  have hp : normalizedUnitOrder L (.ofMul p) = 1 := by
    change normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) (localUniformizer K))) = 1
    rw [normalizedUnitOrder_map_uniformizer, he, Nat.cast_one]
  have hb : normalizedUnitOrder L (.ofMul (b / p ^ z)) = 0 := by
    rw [ofMul_div, map_sub, ofMul_zpow, map_zsmul, hp, zsmul_eq_mul, mul_one]
    exact sub_self z
  obtain ⟨x, hx⟩ := exists_localIntegerUnitsInclusion L _ hb
  have hnorm : normalizedUnitOrder K (.ofMul (normUnits K L (b / p ^ z))) = 0 := by
    rw [← hx, normUnits_localIntegerUnitsInclusion K L hcont, localIntegerUnitsInclusion_order]
  dsimp only [p] at hnorm
  rw [map_div, map_zpow, ofMul_div, map_sub, ofMul_zpow, map_zsmul,
    normUnits_base, ofMul_pow, map_nsmul, normalizedUnitOrder_localUniformizer] at hnorm
  simpa [z, mul_comm] using sub_eq_zero.mp hnorm

/-- The actual norm image in an unramified extension is detected by order modulo the degree. -/
theorem mem_normSubgroup_iff_of_localUnramified (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) (a : Kˣ) :
    a ∈ normSubgroup K L ↔
      (Module.finrank K L : ℤ) ∣ normalizedUnitOrder K (.ofMul a) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, normalizedUnitOrder_norm_of_unramified K L hcont he b⟩
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := normalizedUnitOrder_surjective L k
    have h : normalizedUnitOrder K (.ofMul (a / normUnits K L b.toMul)) = 0 := by
      rw [ofMul_div, map_sub, normalizedUnitOrder_norm_of_unramified K L hcont he,
        ofMul_toMul, hb, hk, sub_self]
    obtain ⟨y, hy⟩ := exists_localIntegerUnitsInclusion K _ h
    obtain ⟨x, rfl⟩ := localIntegerNorm_surjective K L hcont he y
    refine ⟨localIntegerUnitsInclusion L x * b.toMul, ?_⟩
    rw [map_mul, normUnits_localIntegerUnitsInclusion K L hcont, hy, div_mul_cancel]

end Langlands.ClassFieldTheory.Local
