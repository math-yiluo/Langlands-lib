import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.Padics.LocalField

/-!
# P-adic realization of a characteristic-zero local field

For a characteristic-zero nonarchimedean local field `F` with residue
characteristic `p`, the rational embedding extends to a continuous map
`ℚ_[p] →+* F`. This makes `F` a finite extension of `ℚ_[p]` with its original
carrier, field, topology and valuative relation. The two packages are
`Langlands.CharZeroLocalField.padicField` and
`Langlands.CharZeroLocalField.topologicalData`.

See the paired Markdown for the comparison with Serre, *Local Fields*,
Chapter II, §5, and the proof via local compactness.
-/

noncomputable section

open ValuativeRel

namespace Langlands.CharZeroLocalField

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue characteristic of a nonarchimedean local field. -/
def residueChar : ℕ := ringChar 𝓀[F]

theorem residueChar_prime : (residueChar F).Prime :=
  CharP.prime_ringChar 𝓀[F]

instance fact_residueChar_prime : Fact (residueChar F).Prime := ⟨residueChar_prime F⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Natural numbers have valuation at most one. -/
theorem valuation_natCast_le_one (m : ℕ) : valuation F (m : F) ≤ 1 := by
  have h := (m : 𝒪[F]).2
  rw [Valuation.mem_integer_iff] at h
  simpa using h

/-- A natural number has valuation one when it is not divisible by the residue
characteristic. -/
theorem valuation_natCast_eq_one {m : ℕ} (hm : ¬ residueChar F ∣ m) :
    valuation F (m : F) = 1 := by
  have h1 : (IsLocalRing.residue 𝒪[F] (m : 𝒪[F])) ≠ 0 := by
    rw [map_natCast]
    exact fun h => hm ((ringChar.spec 𝓀[F] m).1 h)
  have h2 : IsUnit (m : 𝒪[F]) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  have := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation F))).1 h2
  simpa using this

/-- The residue characteristic has valuation less than one. -/
theorem valuation_residueChar_lt_one : valuation F (residueChar F : F) < 1 := by
  have h1 : (IsLocalRing.residue 𝒪[F] (residueChar F : 𝒪[F])) = 0 := by
    rw [map_natCast]
    exact ringChar.Nat.cast_ringChar
  have h2 : ¬ IsUnit (residueChar F : 𝒪[F]) := fun h =>
    (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h1
  have h3 := (valuation_natCast_le_one F (residueChar F))
  refine lt_of_le_of_ne h3 fun h => h2 ?_
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation F))).2 (by simpa using h)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Integers have valuation at most one. -/
theorem valuation_intCast_le_one (m : ℤ) : valuation F (m : F) ≤ 1 := by
  have h := (m : 𝒪[F]).2
  rw [Valuation.mem_integer_iff] at h
  simpa using h

/-- A rational number which is integral at `p` has valuation at most one. -/
theorem valuation_ratCast_le_one {q : ℚ} (hq : ‖(q : ℚ_[residueChar F])‖ ≤ 1) :
    valuation F (q : F) ≤ 1 := by
  have hden : ¬ residueChar F ∣ q.den := by
    rwa [Padic.norm_rat_le_one_iff_padicValuation_le_one, Rat.padicValuation_le_one_iff] at hq
  rw [Rat.cast_def, map_div₀, valuation_natCast_eq_one F hden, div_one]
  exact valuation_intCast_le_one F q.num

section CharZero

variable [CharZero F]

/-- Rational numbers that are `p`-adically small are small in `F`. -/
theorem exists_norm_lt_valuation_lt (γ : (ValueGroupWithZero F)ˣ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, ‖(q : ℚ_[residueChar F])‖ < ε → valuation F (q : F) < γ := by
  obtain ⟨N, hN⟩ := exists_pow_lt₀ (valuation_residueChar_lt_one F) γ
  have hp0 : (residueChar F : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (residueChar_prime F).ne_zero
  have hpN : ((residueChar F : ℚ) ^ N) ≠ 0 := pow_ne_zero _ hp0
  refine ⟨‖(((residueChar F : ℚ) ^ N : ℚ) : ℚ_[residueChar F])‖, ?_, fun q hq => ?_⟩
  · exact norm_pos_iff.2 (Rat.cast_ne_zero.2 hpN)
  have h1 : ‖((q / (residueChar F : ℚ) ^ N : ℚ) : ℚ_[residueChar F])‖ ≤ 1 := by
    rw [Rat.cast_div, norm_div]
    exact (div_le_one (lt_of_le_of_lt (norm_nonneg _) hq)).2 hq.le
  have h2 := valuation_ratCast_le_one F h1
  have h3 : (q : F) = ((q / (residueChar F : ℚ) ^ N : ℚ) : F) * (residueChar F : F) ^ N := by
    rw [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, div_mul_cancel₀]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (residueChar_prime F).ne_zero)
  rw [h3, map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) hN

/-- The uniform structure on `F` determined by its additive topological group structure. -/
local instance uniformSpace : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F

local instance isUniformAddGroup : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup

local instance t2Space : T2Space F := HarmonicAnalysis.GeneralLocalField.t2Space F

/-- The rational embedding, on `ℚ` with its `p`-adic uniform structure. -/
abbrev ratCastWithVal : WithVal (Rat.padicValuation (residueChar F)) →+* F :=
  (Rat.castHom F).comp (WithVal.equiv (Rat.padicValuation (residueChar F))).toRingHom

theorem uniformContinuous_ratCastWithVal : UniformContinuous (ratCastWithVal F) := by
  refine uniformContinuous_of_continuousAt_zero (ratCastWithVal F).toAddMonoidHom ?_
  rw [ContinuousAt, Padic.isUniformInducing_cast_withVal.isInducing.nhds_eq_comap]
  simp only [map_zero, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rw [(Metric.nhds_basis_ball.comap _).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero F)]
  intro γ _
  obtain ⟨ε, hε, h⟩ := exists_norm_lt_valuation_lt F γ
  exact ⟨ε, hε, fun x hx => h _ (by simpa using hx)⟩

/-- The continuous embedding of `ℚ_p` into a characteristic-zero local field of
residue characteristic `p`. -/
def padicEmbedding : ℚ_[residueChar F] →+* F :=
  IsDenseInducing.extendRingHom Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratCastWithVal F)

theorem continuous_padicEmbedding : Continuous (padicEmbedding F) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratCastWithVal F)).continuous

/-- Elements of `ℤ_p` are mapped to integers of `F`. -/
theorem valuation_padicEmbedding_le_one {x : ℚ_[residueChar F]} (hx : ‖x‖ ≤ 1) :
    valuation F (padicEmbedding F x) ≤ 1 := by
  let S : Set ℚ_[residueChar F] := padicEmbedding F ⁻¹' ((valuation F).integer : Set F)
  have hS : IsClosed S :=
    (Valuation.isClosed_integer (v := valuation F)).preimage (continuous_padicEmbedding F)
  have hball : IsOpen (Metric.closedBall (0 : ℚ_[residueChar F]) 1) :=
    IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hsub : Metric.closedBall (0 : ℚ_[residueChar F]) 1 ⊆
      closure (Metric.closedBall 0 1 ∩ Set.range ((↑) : ℚ → ℚ_[residueChar F])) :=
    (Padic.denseRange_ratCast _).open_subset_closure_inter hball
  have hsub2 : Metric.closedBall (0 : ℚ_[residueChar F]) 1 ∩
      Set.range ((↑) : ℚ → ℚ_[residueChar F]) ⊆ S := by
    rintro _ ⟨hy, q, rfl⟩
    simp only [S, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_ratCast]
    exact valuation_ratCast_le_one F (by simpa using hy)
  have := hS.closure_subset_iff.2 hsub2 (hsub (by simpa using hx))
  simpa [S, Valuation.mem_integer_iff] using this

/-- Conversely, an element of `ℚ_p` whose image in `F` is integral lies in `ℤ_p`. -/
theorem norm_le_one_of_valuation_padicEmbedding_le_one {x : ℚ_[residueChar F]}
    (hx : valuation F (padicEmbedding F x) ≤ 1) : ‖x‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (by norm_num)
  have hp : (residueChar F : ℚ_[residueChar F]) ≠ 0 :=
    Nat.cast_ne_zero.2 (residueChar_prime F).ne_zero
  have hinv : ‖x⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have hinv' : ‖x⁻¹‖ ≤ (residueChar F : ℝ) ^ (-1 : ℤ) :=
    (Padic.norm_le_pow_iff_norm_lt_pow_add_one x⁻¹ (-1)).2 (by simpa using hinv)
  have hy : ‖x⁻¹ / (residueChar F : ℚ_[residueChar F])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_inv_eq_mul]
    have hp0 : (0 : ℝ) < residueChar F := by exact_mod_cast (residueChar_prime F).pos
    calc ‖x⁻¹‖ * (residueChar F : ℝ) ≤ (residueChar F : ℝ) ^ (-1 : ℤ) * residueChar F :=
          mul_le_mul_of_nonneg_right hinv' hp0.le
      _ = 1 := by rw [zpow_neg_one, inv_mul_cancel₀ hp0.ne']
  have h1 := valuation_padicEmbedding_le_one F hy
  have h2 : valuation F (padicEmbedding F x⁻¹) < 1 := by
    have : x⁻¹ = x⁻¹ / (residueChar F : ℚ_[residueChar F]) * residueChar F := by
      rw [div_mul_cancel₀ _ hp]
    rw [this, map_mul, map_mul, map_natCast]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) (valuation_residueChar_lt_one F)
  have h3 : valuation F (padicEmbedding F (x * x⁻¹)) < 1 := by
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) h2
  rw [mul_inv_cancel₀ hx0, map_one, map_one] at h3
  exact lt_irrefl _ h3

theorem valuation_padicEmbedding_le_one_iff (x : ℚ_[residueChar F]) :
    valuation F (padicEmbedding F x) ≤ 1 ↔ ‖x‖ ≤ 1 :=
  ⟨norm_le_one_of_valuation_padicEmbedding_le_one F, valuation_padicEmbedding_le_one F⟩

/-- The valuation of `F` restricted along `ℚ_p → F` is equivalent to the `p`-adic valuation. -/
theorem isEquiv_comap_padicEmbedding :
    ((valuation F).comap (padicEmbedding F)).IsEquiv Padic.mulValuation := by
  refine Valuation.isEquiv_of_val_le_one fun x => ?_
  rw [Valuation.comap_apply, valuation_padicEmbedding_le_one_iff]
  simpa [not_lt] using (Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := x)).not

/-- The `ℚ_p`-algebra structure of a characteristic-zero local field given by
`padicEmbedding`. Install with `letI := padicAlgebra F` when needed;
this does not replace a caller's existing algebra structure. -/
@[instance_reducible]
def padicAlgebra : Algebra ℚ_[residueChar F] F := (padicEmbedding F).toAlgebra

theorem algebraMap_padicAlgebra :
    @algebraMap ℚ_[residueChar F] F _ _ (padicAlgebra F) = padicEmbedding F := rfl

theorem continuousSMul :
    letI := padicAlgebra F
    ContinuousSMul ℚ_[residueChar F] F :=
  letI := padicAlgebra F
  continuousSMul_of_algebraMap _ _ (continuous_padicEmbedding F)

theorem finiteDimensional :
    letI := padicAlgebra F
    FiniteDimensional ℚ_[residueChar F] F :=
  letI := padicAlgebra F
  haveI := continuousSMul F
  FiniteDimensional.of_locallyCompactSpace ℚ_[residueChar F]

theorem isModuleTopology :
    letI := padicAlgebra F
    IsModuleTopology ℚ_[residueChar F] F :=
  letI := padicAlgebra F
  haveI := continuousSMul F
  haveI := finiteDimensional F
  isModuleTopologyOfFiniteDimensional

theorem valuativeExtension :
    letI := padicAlgebra F
    ValuativeExtension ℚ_[residueChar F] F := by
  let := padicAlgebra F
  refine ⟨fun a b => ?_⟩
  rw [Valuation.vle_iff_le (valuation F), Valuation.vle_iff_le Padic.mulValuation]
  exact isEquiv_comap_padicEmbedding F a b

/-- A characteristic-zero nonarchimedean local field, viewed as a finite extension
of `ℚ_p` for its residue characteristic `p`. -/
def padicField : PadicField.{u} (residueChar F) :=
  letI := padicAlgebra F
  haveI := finiteDimensional F
  PadicField.ofField F

/-- The given topology and valuation of `F` as topological data of `padicField F`. -/
def topologicalData : (padicField F).TopologicalData where
  topology := inferInstanceAs (TopologicalSpace F)
  valuativeRel := inferInstanceAs (ValuativeRel F)
  valuativeExtension := by exact valuativeExtension F
  moduleTopology := by exact isModuleTopology F
  localField := inferInstanceAs (IsNonarchimedeanLocalField F)

@[simp] theorem padicField_carrier : (padicField F).Carrier = F := rfl

theorem padicField_field : HEq (padicField F).field ‹Field F› := HEq.rfl

theorem topologicalData_topology :
    (topologicalData F).topology = ‹TopologicalSpace F› := rfl

theorem topologicalData_valuativeRel :
    (topologicalData F).valuativeRel = ‹ValuativeRel F› := rfl

theorem topologicalData_localField :
    HEq (topologicalData F).localField ‹IsNonarchimedeanLocalField F› := HEq.rfl

end CharZero

end Langlands.CharZeroLocalField
