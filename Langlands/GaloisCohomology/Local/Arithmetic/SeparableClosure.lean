import Langlands.GaloisCohomology.Local.Arithmetic.Uniqueness
import Langlands.LocalField.FiniteExtension
import Langlands.Galois.Local.SpectralDefinitions

/-!
# Valuations on algebraic extensions and on their intermediate fields

For a nonarchimedean local field `K` and an algebraic extension `Ω` (for instance a separable
closure), every valuative relation on `Ω` extending that of `K` is given by Mathlib's spectral
norm (`vle_iff_spectralNorm_le`); in particular it is unique and invariant under
`Ω ≃ₐ[K] Ω`. The spectral norm supplies such a relation and a topology on `Ω`
(`algebraicValuativeRel`, `algebraicTopology`).

An intermediate field `E` of `Ω` carries the restricted relation; these instances are scoped, in
the namespace `IntermediateFieldStructure`. With them, a finite intermediate field of an
algebraic extension with valuative topology is a nonarchimedean local field (its structure is the
Library's spectral structure `LocalField.FiniteExtension`).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel Topology Filter Polynomial

section Integral

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [ValuativeExtension K L]

theorem valuation_le_one_of_aeval_eq_zero {p : K[X]} (hp : p.Monic)
    (hc : ∀ n, valuation K (p.coeff n) ≤ 1) {y : L} (hy : aeval y p = 0) :
    valuation L y ≤ 1 := by
  by_contra h
  push Not at h
  set d := p.natDegree
  have hsum : aeval y p = y ^ d + ∑ i ∈ Finset.range d, algebraMap K L (p.coeff i) * y ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul, add_comm]
    simp only [Algebra.smul_def]
    rfl
  rw [hsum, add_eq_zero_iff_eq_neg] at hy
  have hy0 : valuation L y ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one h))
  have hlt : valuation L (∑ i ∈ Finset.range d, algebraMap K L (p.coeff i) * y ^ i) <
      valuation L y ^ d := by
    refine Valuation.map_sum_lt _ hy0 fun i hi ↦ ?_
    rw [map_mul, map_pow]
    have hci : valuation L (algebraMap K L (p.coeff i)) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr (hc i)
    calc valuation L (algebraMap K L (p.coeff i)) * valuation L y ^ i
        ≤ 1 * valuation L y ^ i := mul_le_mul_left hci _
      _ = valuation L y ^ i := one_mul _
      _ < valuation L y ^ d := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  rw [← map_pow, hy, Valuation.map_neg] at hlt
  exact lt_irrefl _ hlt

end Integral

section Spectral

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The spectral norm on an algebraic extension of `K` (for the Library's norm on `K`,
`LocalGalois.localNormedField`). -/
@[instance_reducible]
def algebraicNormedField : NontriviallyNormedField L :=
  letI := LocalGalois.localNormedField K
  haveI := LocalGalois.localNormedField_ultrametric K
  haveI := LocalGalois.localNormedField_complete K
  spectralNorm.nontriviallyNormedField K L

theorem algebraicNormedField_isUltrametricDist :
    letI := algebraicNormedField K L
    IsUltrametricDist L := by
  let := LocalGalois.localNormedField K
  have := LocalGalois.localNormedField_ultrametric K
  have := LocalGalois.localNormedField_complete K
  let := algebraicNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

theorem algebraicNormedField_norm_algebraMap (a : K) :
    letI := LocalGalois.localNormedField K
    letI := algebraicNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := LocalGalois.localNormedField K
  have := LocalGalois.localNormedField_ultrametric K
  have := LocalGalois.localNormedField_complete K
  exact spectralNorm_extends a

variable {K} in
theorem localNormedField_le_iff_vle (x y : K) :
    letI := LocalGalois.localNormedField K
    ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y := by
  rw [LocalGalois.localNormedField_le, (valuation K).vle_iff_le]

variable {K L}

theorem valuation_le_one_of_spectralNorm_le_one [ValuativeRel L] [ValuativeExtension K L] {y : L}
    (h : letI := LocalGalois.localNormedField K; spectralNorm K L y ≤ 1) :
    valuation L y ≤ 1 := by
  let := LocalGalois.localNormedField K
  have := LocalGalois.localNormedField_ultrametric K
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hc := (spectralValue_le_one_iff (minpoly.monic hint)).mp h
  refine valuation_le_one_of_aeval_eq_zero (minpoly.monic hint) (fun n ↦ ?_) (minpoly.aeval K y)
  have h1 : ‖(minpoly K y).coeff n‖ ≤ ‖(1 : K)‖ := by rw [norm_one]; exact hc n
  rw [localNormedField_le_iff_vle, (valuation K).vle_iff_le, map_one] at h1
  exact h1

theorem valuation_lt_one_iff_spectralNorm_lt_one [ValuativeRel L] [ValuativeExtension K L]
    (x : L) :
    valuation L x < 1 ↔ (letI := LocalGalois.localNormedField K; spectralNorm K L x < 1) := by
  let := LocalGalois.localNormedField K
  let := algebraicNormedField K L
  change valuation L x < 1 ↔ ‖x‖ < 1
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hn
      exact absurd hn (by norm_num)
    have hinv : valuation L x⁻¹ ≤ 1 := by
      refine valuation_le_one_of_spectralNorm_le_one (K := K) ?_
      change ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hn
    rw [map_inv₀] at hinv
    have hv0 : valuation L x ≠ 0 := by simpa using hx0
    have := mul_le_mul_right hinv (valuation L x)
    rw [mul_inv_cancel₀ hv0, mul_one] at this
    exact absurd hx this.not_gt
  · intro hx
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha0 hx
    have ha : a ≠ 0 := norm_pos_iff.mp ha0
    have hna : algebraMap K L a ≠ 0 := (_root_.map_ne_zero _).mpr ha
    have hnorm : ‖algebraMap K L a‖ = ‖a‖ := algebraicNormedField_norm_algebraMap K L a
    set u := x ^ n * (algebraMap K L a)⁻¹ with hu
    have hu1 : valuation L u ≤ 1 := by
      refine valuation_le_one_of_spectralNorm_le_one (K := K) ?_
      change ‖u‖ ≤ 1
      rw [hu, norm_mul, norm_inv, norm_pow, hnorm]
      exact mul_inv_le_one_of_le₀ hn.le (norm_nonneg _)
    have hva : valuation L (algebraMap K L a) < 1 := by
      refine (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr ?_
      have : ¬ ‖(1 : K)‖ ≤ ‖a‖ := by rw [norm_one]; exact not_le.mpr ha1
      rw [localNormedField_le_iff_vle, (valuation K).vle_iff_le, map_one] at this
      exact not_le.mp this
    have hxn : x ^ n = u * algebraMap K L a := by
      rw [hu, mul_assoc, inv_mul_cancel₀ hna, mul_one]
    have hpow : valuation L x ^ n < 1 := by
      rw [← map_pow, hxn, map_mul]
      calc valuation L u * valuation L (algebraMap K L a)
          ≤ 1 * valuation L (algebraMap K L a) := mul_le_mul_left hu1 _
        _ < 1 := by rw [one_mul]; exact hva
    by_contra h
    exact (one_le_pow₀ (not_lt.mp h)).not_gt hpow

/-- Every valuative relation on an algebraic extension of `K` extending that of `K` compares
elements by their spectral norms. -/
theorem vle_iff_spectralNorm_le [ValuativeRel L] [ValuativeExtension K L] (x y : L) :
    x ≤ᵥ y ↔ (letI := LocalGalois.localNormedField K; spectralNorm K L x ≤ spectralNorm K L y) := by
  let := LocalGalois.localNormedField K
  let := algebraicNormedField K L
  change x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, norm_nonneg, iff_true]
    exact ValuativeRel.zero_vle y
  · rw [vle_iff_not_valuation_div_lt_one hx, valuation_lt_one_iff_spectralNorm_lt_one (K := K)]
    change ¬ ‖y / x‖ < 1 ↔ _
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx), not_lt]

variable (K) in
/-- Uniqueness of the extension of the valuative relation to an algebraic extension. -/
theorem valuativeRel_eq_of_isAlgebraic {v₁ v₂ : ValuativeRel L}
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  ext x y
  exact (@vle_iff_spectralNorm_le K _ _ _ _ L _ _ _ v₁ e₁ x y).trans
    (@vle_iff_spectralNorm_le K _ _ _ _ L _ _ _ v₂ e₂ x y).symm

theorem valuation_algEquiv_apply_of_isAlgebraic [ValuativeRel L] [ValuativeExtension K L]
    (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by
  let := LocalGalois.localNormedField K
  have h : spectralNorm K L (σ x) = spectralNorm K L x := (spectralNorm_eq_of_equiv σ x).symm
  refine le_antisymm ?_ ?_
  · rw [← (valuation L).vle_iff_le, vle_iff_spectralNorm_le (K := K), h]
  · rw [← (valuation L).vle_iff_le, vle_iff_spectralNorm_le (K := K), h]

end Spectral

section Existence

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The valuative relation of the spectral norm on an algebraic extension. -/
@[instance_reducible]
def algebraicValuativeRel : ValuativeRel L :=
  letI := algebraicNormedField K L
  haveI := algebraicNormedField_isUltrametricDist K L
  ValuativeRel.ofValuation (NormedField.valuation (K := L))

/-- The topology of the spectral norm on an algebraic extension. -/
@[instance_reducible]
def algebraicTopology : TopologicalSpace L :=
  (algebraicNormedField K L).toUniformSpace.toTopologicalSpace

theorem algebraicValuativeRel_vle_iff (x y : L) :
    letI := LocalGalois.localNormedField K
    letI := algebraicValuativeRel K L
    x ≤ᵥ y ↔ spectralNorm K L x ≤ spectralNorm K L y := Iff.rfl

theorem algebraicValuativeRel_valuativeExtension :
    letI := algebraicValuativeRel K L
    ValuativeExtension K L := by
  let := algebraicValuativeRel K L
  constructor
  intro a b
  rw [algebraicValuativeRel_vle_iff]
  let := LocalGalois.localNormedField K
  rw [← localNormedField_le_iff_vle]
  rw [← algebraicNormedField_norm_algebraMap K L a, ← algebraicNormedField_norm_algebraMap K L b]
  rfl

theorem algebraicTopology_isValuativeTopology :
    letI := algebraicValuativeRel K L
    letI := algebraicTopology K L
    IsValuativeTopology L := by
  let := algebraicNormedField K L
  have := algebraicNormedField_isUltrametricDist K L
  let := algebraicValuativeRel K L
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
    (fun {s} ↦ (NormedField.toValued (K := L)).is_topological_valuation s)

end Existence

/-! ### Intermediate fields -/

namespace IntermediateFieldStructure

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
  (E : IntermediateField K L)

/-- The valuative relation of `L` restricted to an intermediate field. -/
scoped instance intermediateField_valuativeRel : ValuativeRel E :=
  ValuativeRel.ofValuation ((valuation L).comap (algebraMap E L))

variable {E} in
@[simp]
theorem intermediateField_coe_vle_coe_iff (x y : E) : (x : L) ≤ᵥ (y : L) ↔ x ≤ᵥ y :=
  (valuation L).vle_iff_le

scoped instance intermediateField_valuativeExtension_right : ValuativeExtension E L :=
  ⟨intermediateField_coe_vle_coe_iff⟩

scoped instance intermediateField_valuativeExtension_left [ValuativeRel K]
    [ValuativeExtension K L] : ValuativeExtension K E :=
  ⟨fun a b ↦ by
    rw [← intermediateField_coe_vle_coe_iff, IntermediateField.coe_algebraMap_apply,
      IntermediateField.coe_algebraMap_apply, ValuativeExtension.vle_iff_vle]⟩

variable {E} in
theorem intermediateField_valuation_coe (x : E) :
    valuation L (x : L) = ValuativeExtension.mapValueGroupWithZero E L (valuation E x) :=
  (ValuativeExtension.mapValueGroupWithZero_valuation (A := E) (B := L) x).symm

theorem valuativeExtension_inclusion {E F : IntermediateField K L} (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F :=
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  ⟨fun a b ↦ by
    rw [← intermediateField_coe_vle_coe_iff (L := L) a b, ← intermediateField_coe_vle_coe_iff (L := L)]
    rfl⟩

end IntermediateFieldStructure

open IntermediateFieldStructure

section Topology

theorem topologicalSpace_eq_of_isValuativeTopology {R : Type*} [CommRing R] [ValuativeRel R]
    {t₁ t₂ : TopologicalSpace R} (h₁ : @IsValuativeTopology R _ _ t₁)
    (h₂ : @IsValuativeTopology R _ _ t₂) : t₁ = t₂ :=
  TopologicalSpace.ext_nhds fun x ↦ Filter.ext fun s ↦
    (@IsValuativeTopology.mem_nhds_iff R _ _ t₁ h₁ s x).trans
      (@IsValuativeTopology.mem_nhds_iff R _ _ t₂ h₂ s x).symm

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] in
theorem exists_algebraMap_valuation_lt (γ : (ValueGroupWithZero Ω)ˣ) :
    ∃ a : K, a ≠ 0 ∧ valuation Ω (algebraMap K Ω a) < γ := by
  let := LocalGalois.localNormedField K
  let := algebraicNormedField K Ω
  obtain ⟨z, hz⟩ := valuation_surjective (γ : ValueGroupWithZero Ω)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact γ.ne_zero hz.symm
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hz0) ha1
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  refine ⟨a ^ n, pow_ne_zero _ ha, ?_⟩
  rw [← hz, ← (valuation Ω).vlt_iff_lt, ← not_vle, vle_iff_spectralNorm_le (K := K), not_le]
  change ‖algebraMap K Ω (a ^ n)‖ < ‖z‖
  rw [algebraicNormedField_norm_algebraMap K Ω, norm_pow]
  exact hn

/-- An intermediate field of an algebraic extension with valuative topology has the valuative
topology for the restricted relation. -/
theorem intermediateField_isValuativeTopology (E : IntermediateField K Ω) :
    IsValuativeTopology E := by
  have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := E) (B := Ω)
  have hval := intermediateField_valuation_coe (E := E)
  have : ContinuousConstVAdd E E :=
    ⟨fun c ↦ continuous_induced_rng.2 (continuous_const.add continuous_subtype_val)⟩
  refine IsValuativeTopology.of_zero fun s ↦ ?_
  have hb := (IsValuativeTopology.hasBasis_nhds_zero Ω).comap ((↑) : E → Ω)
  rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero]
  refine hb.mem_iff.trans ?_
  constructor
  · rintro ⟨γ, -, hγ⟩
    obtain ⟨a, ha0, ha⟩ := exists_algebraMap_valuation_lt (K := K) γ
    set b : E := algebraMap K E a
    have hb0 : b ≠ 0 := (_root_.map_ne_zero _).mpr ha0
    have hbv : valuation Ω (b : Ω) < γ := by
      rw [IntermediateField.coe_algebraMap_apply]
      exact ha
    refine ⟨Units.mk0 (valuation E b) (by simpa using hb0), fun z hz ↦ hγ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [hval] at hbv ⊢
    exact (hmono hz).trans hbv
  · rintro ⟨γ, hγ⟩
    have hγ0 : ValuativeExtension.mapValueGroupWithZero E Ω γ ≠ 0 := by
      rw [← map_zero (ValuativeExtension.mapValueGroupWithZero E Ω)]
      exact (hmono (zero_lt_iff.mpr γ.ne_zero)).ne'
    refine ⟨Units.mk0 _ hγ0, trivial, fun z hz ↦ hγ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [hval] at hz
    exact hmono.lt_iff_lt.mp hz

end Topology

section Finite

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The Library's spectral valuative relation on a finite extension extends that of `K`. -/
theorem spectral_valuativeExtension (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI := LocalField.FiniteExtension.valuativeRel K L
    ValuativeExtension K L :=
  letI := LocalField.FiniteExtension.valuativeRel K L
  ⟨LocalField.FiniteExtension.algebraMap_vle_iff K L⟩

/-- On a finite extension, every valuative relation extending that of `K` is the Library's
spectral one. -/
theorem valuativeRel_eq_spectral {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [v : ValuativeRel L] [ValuativeExtension K L] :
    v = LocalField.FiniteExtension.valuativeRel K L :=
  valuativeRel_eq_of_isAlgebraic K inferInstance (spectral_valuativeExtension K L)

variable {K}
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

/-- A finite intermediate field of an algebraic extension with valuative topology is a
nonarchimedean local field. -/
theorem intermediateField_isNonarchimedeanLocalField (L : IntermediateField K Ω)
    [FiniteDimensional K L] : IsNonarchimedeanLocalField L := by
  have hrel := valuativeRel_eq_spectral K (L := L)
  have h1 := LocalField.FiniteExtension.isLocalField K L
  rw [← hrel] at h1
  have hvt : IsValuativeTopology L := intermediateField_isValuativeTopology L
  have ht := topologicalSpace_eq_of_isValuativeTopology hvt h1.toIsValuativeTopology
  rw [← ht] at h1
  exact h1

end Finite

namespace IntermediateFieldStructure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

scoped instance intermediateField_isNonarchimedeanLocalField_of_finiteDimensional
    (L : IntermediateField K Ω) [FiniteDimensional K L] : IsNonarchimedeanLocalField L :=
  Local.intermediateField_isNonarchimedeanLocalField L

end IntermediateFieldStructure

end Langlands.GaloisCohomology.Local
