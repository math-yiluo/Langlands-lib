import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.NormalizedCharacter

/-! # Units through continuous isomorphisms of completions with local fields -/

noncomputable section

namespace Langlands.Global.HarrisDatum

open Filter Topology NumberField IsDedekindDomain

/-- Topological nilpotence is preserved by continuous ring homomorphisms. -/
theorem tendsto_pow_map {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) {x : R}
    (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have := (hf.tendsto 0).comp h
  simpa [Function.comp_def, map_pow, map_zero] using this

theorem valued_lt_one_iff_tendsto {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  Valued.toNormedField.norm_lt_one_iff.symm.trans tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.symm

theorem canonicalNorm_lt_one_iff_tendsto {p : ℕ} [Fact p.Prime] {K : PadicField p}
    (T : K.TopologicalData) (x : K.Carrier) :
    K.canonicalNorm x < 1 ↔
      @Tendsto ℕ K.Carrier (fun n : ℕ => x ^ n) atTop (@nhds K.Carrier T.topology 0) := by
  rw [T.topology_eq_canonicalNormTopology]
  let _ := K.canonicalNormedField
  exact (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one (x := x)).symm

section Units

variable {p : ℕ} [Fact p.Prime] {K' : PadicField p}

theorem canonicalNorm_eq_one_iff {y : K'.Carrier} (hy : y ≠ 0) :
    K'.canonicalNorm y = 1 ↔ ¬ K'.canonicalNorm y < 1 ∧ ¬ K'.canonicalNorm y⁻¹ < 1 := by
  let _ := K'.canonicalNormedField
  change ‖y‖ = 1 ↔ ¬ ‖y‖ < 1 ∧ ¬ ‖y⁻¹‖ < 1
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [norm_inv, inv_lt_one₀ hpos]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)

theorem discreteValuation_eq_one_iff (T : K'.TopologicalData) (y : K'.Carrier) :
    T.discreteValuation y = 1 ↔ K'.canonicalNorm y = 1 := by
  rw [← T.normalizedAbs_eq_one_iff_discreteValuation, T.normalizedAbs_eq_canonicalNorm_pow_degree]
  have hd : Module.finrank (Padic p) K'.Carrier ≠ 0 := Module.finrank_pos.ne'
  exact pow_eq_one_iff_of_nonneg (spectralNorm_nonneg y) hd

end Units

section Completion

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_eq_one_iff {x : v.adicCompletion K} (hx : x ≠ 0) :
    Valued.v x = 1 ↔ ¬ Valued.v x < 1 ∧ ¬ Valued.v x⁻¹ < 1 := by
  have h0 : Valued.v x ≠ 0 := (map_ne_zero _).mpr hx
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr h0)]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)

variable {p : ℕ} [Fact p.Prime] {K' : PadicField p} (T : K'.TopologicalData)
  (φ : v.adicCompletion K ≃+* K'.Carrier)

/-- A continuous isomorphism of a completion with a local field matches the valuation-one
elements with the norm-one elements. -/
theorem valued_symm_eq_one (hφ : @Continuous _ _ _ T.topology φ) {y : K'.Carrier}
    (hy : K'.canonicalNorm y = 1) : Valued.v (φ.symm y) = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [PadicField.canonicalNorm, spectralNorm_zero] at hy
  have hx0 : φ.symm y ≠ 0 := by simpa using hy0
  rw [valued_eq_one_iff v hx0]
  obtain ⟨h1, h2⟩ := (canonicalNorm_eq_one_iff hy0).mp hy
  refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · rw [canonicalNorm_lt_one_iff_tendsto T]
    have := @tendsto_pow_map _ _ _ _ _ T.topology φ.toRingHom hφ _
      ((valued_lt_one_iff_tendsto v _).mp h)
    simpa using this
  · rw [canonicalNorm_lt_one_iff_tendsto T]
    have := @tendsto_pow_map _ _ _ _ _ T.topology φ.toRingHom hφ _
      ((valued_lt_one_iff_tendsto v _).mp h)
    simpa [map_inv₀] using this

end Completion

section Components

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  {p : ℕ} [Fact p.Prime] {K' : PadicField p} [tK : TopologicalSpace K'.Carrier]
  (T : K'.TopologicalData) (hT : T.topology = tK)
  (φ : v.adicCompletion K ≃+* K'.Carrier) (hφ : Continuous φ)

include hT hφ in
theorem valued_symm_eq_one' {y : K'.Carrier} (hy : K'.canonicalNorm y = 1) :
    Valued.v (φ.symm y) = 1 :=
  valued_symm_eq_one v T φ (by subst hT; exact hφ) hy

omit tK in
theorem canonicalNorm_inv_eq_one {y : K'.Carrier} (hy : K'.canonicalNorm y = 1) :
    K'.canonicalNorm y⁻¹ = 1 := by
  let _ := K'.canonicalNormedField
  change ‖y⁻¹‖ = 1
  rw [norm_inv]
  change (K'.canonicalNorm y)⁻¹ = 1
  rw [hy, inv_one]

/-- The unit of the completed integers corresponding to a norm-one unit of `K'`. -/
def integralUnit (u : K'.Carrierˣ) (hu : K'.canonicalNorm u = 1) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨φ.symm u, (valued_symm_eq_one' v T hT φ hφ hu).le⟩
  inv := ⟨φ.symm ((u⁻¹ : K'.Carrierˣ) : K'.Carrier), (valued_symm_eq_one' v T hT φ hφ (by
    rw [Units.val_inv_eq_inv_val]; exact canonicalNorm_inv_eq_one hu)).le⟩
  val_inv := Subtype.ext (by
    change φ.symm (u : K'.Carrier) * φ.symm ((u⁻¹ : K'.Carrierˣ) : K'.Carrier) = 1
    rw [← map_mul, Units.mul_inv, map_one])
  inv_val := Subtype.ext (by
    change φ.symm ((u⁻¹ : K'.Carrierˣ) : K'.Carrier) * φ.symm (u : K'.Carrier) = 1
    rw [← map_mul, Units.inv_mul, map_one])

theorem integralUnit_coe (u : K'.Carrierˣ) (hu : K'.canonicalNorm u = 1) :
    Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom (integralUnit v T hT φ hφ u hu) =
      Units.map φ.symm.toRingHom.toMonoidHom u :=
  Units.ext rfl

include T hT hφ in
theorem mem_units_of_canonicalNorm (u : K'.Carrierˣ) (hu : K'.canonicalNorm u = 1) :
    Units.map φ.symm.toRingHom.toMonoidHom u ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [← integralUnit_coe v T hT φ hφ u hu]
  exact ⟨(integralUnit v T hT φ hφ u hu).val.2, (integralUnit v T hT φ hφ u hu).inv.2⟩

/-- A character of `K'ˣ` read on the completed units through `φ`. -/
def unitCharacter (χ₀ : K'.Carrierˣ →ₜ* ℂˣ) : (v.adicCompletionIntegers K)ˣ →ₜ* ℂˣ :=
  χ₀.comp
    { toMonoidHom := Units.map (φ.toRingHom.toMonoidHom.comp
        (v.adicCompletionIntegers K).subtype.toMonoidHom)
      continuous_toFun := (hφ.comp continuous_subtype_val).units_map _ }

include T hT in
/-- With unit components prescribed through `φ` and an unramified second factor, the product
character agrees with `χ₀` on the norm-one units, read through `φ`. -/
theorem finiteComponent_mul_eq (X ψ : HeckeCharacter K) (χ₀ : K'.Carrierˣ →ₜ* ℂˣ)
    (hX : ∀ b : (v.adicCompletionIntegers K)ˣ,
      X.finiteComponent v (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom b) =
        unitCharacter v φ hφ χ₀ b)
    (hψ : ψ.IsUnramifiedAt v) (u : K'.Carrierˣ) (hu : K'.canonicalNorm u = 1) :
    (X * ψ).finiteComponent v (Units.map φ.symm.toRingHom.toMonoidHom u) = χ₀ u := by
  rw [HeckeCharacter.finiteComponent_mul, ContinuousMonoidHom.mul_apply,
    hψ _ (mem_units_of_canonicalNorm v T hT φ hφ u hu), mul_one,
    ← integralUnit_coe v T hT φ hφ u hu, hX]
  change χ₀ (Units.map (φ.toRingHom.toMonoidHom.comp
    (v.adicCompletionIntegers K).subtype.toMonoidHom) (integralUnit v T hT φ hφ u hu)) = _
  congr 1
  apply Units.ext
  change φ (φ.symm (u : K'.Carrier)) = u
  exact φ.apply_symm_apply _

end Components

end Langlands.Global.HarrisDatum
