import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute

/-!
# Common-field constructions for Herbrand theory

Restrict field isomorphisms to the supplied integer rings, pull back finite
Galois subfields, and form the finite restriction intersection in an ambient
extension. These constructions are independent of characteristic.
-/

noncomputable section

namespace Langlands.Ramification.Local

open Filter ValuativeRel
open scoped Topology

universe u₀ uK uL₁ uL₂ uΩ₁ uΩ₂

private theorem valuation_lt_one_iff_pow_tendsto
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : L) :
    valuation L x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    let := IsTopologicalAddGroup.rightUniformSpace L
    have := isUniformAddGroup_of_addCommGroup (G := L)
    have : MulArchimedean (ValueGroupWithZero L) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    exact Valued.tendsto_zero_pow_of_v_lt_one hx
  · intro h
    have hball : {z : L | valuation L z < 1} ∈ 𝓝 (0 : L) :=
      (IsValuativeTopology.hasBasis_nhds_zero' L).mem_of_mem (by simp)
    obtain ⟨n, hn⟩ := (h.eventually hball).exists
    contrapose! hn
    exact one_le_pow₀ (a := valuation L x) hn |>.trans_eq (map_pow _ _ _).symm

private theorem preserves_integers_of_continuous_symm
    {L₁ : Type uL₁} {L₂ : Type uL₂} [Field L₁] [Field L₂]
    [ValuativeRel L₁] [ValuativeRel L₂] [TopologicalSpace L₁] [TopologicalSpace L₂]
    [IsNonarchimedeanLocalField L₁] [IsNonarchimedeanLocalField L₂]
    (f : L₁ ≃+* L₂) (hf : Continuous f.symm) {x : L₁} (hx : valuation L₁ x ≤ 1) :
    valuation L₂ (f x) ≤ 1 := by
  by_contra! hy
  have hx0 : x ≠ 0 := fun h => by simp [h] at hy
  have hinv : valuation L₂ ((f x)⁻¹) < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy
  have hpow := (valuation_lt_one_iff_pow_tendsto ((f x)⁻¹)).mp hinv
  have hback : Tendsto (fun n : ℕ => (x⁻¹) ^ n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_pow, map_inv₀, RingEquiv.symm_apply_apply,
      map_zero] using (hf.tendsto 0).comp hpow
  have hval := (valuation_lt_one_iff_pow_tendsto (x⁻¹)).mpr hback
  rw [map_inv₀] at hval
  have hpos : 0 < valuation L₁ x := by simpa only [zero_lt_iff, map_ne_zero] using hx0
  exact (not_lt_of_ge hx) ((inv_lt_one₀ hpos).mp hval)

section FieldEquiv

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L₁ : Type uL₁} {L₂ : Type uL₂} [Field L₁] [Field L₂] [Algebra K₀ L₁] [Algebra K₀ L₂]
  (T₁ : LocalField.TopologicalData K₀ L₁) (T₂ : LocalField.TopologicalData K₀ L₂)
  (K : Type uK) [Field K] [Algebra K₀ K]
  [Algebra K L₁] [IsScalarTower K₀ K L₁] [Algebra K L₂] [IsScalarTower K₀ K L₂]
  (f : L₁ ≃ₐ[K] L₂)

/-- An isomorphism over a common base identifies the supplied valuation rings. -/
theorem map_mem_integers_iff (x : L₁) : f x ∈ T₂.Integers ↔ x ∈ T₁.Integers := by
  let := T₁.topology
  let := T₂.topology
  let := T₁.valuativeRel
  let := T₂.valuativeRel
  let := T₁.moduleTopology
  let := T₂.moduleTopology
  let := T₁.localField
  let := T₂.localField
  have hf : Continuous (f.restrictScalars K₀) :=
    IsModuleTopology.continuous_of_linearMap (f.restrictScalars K₀).toLinearMap
  have hf' : Continuous (f.symm.restrictScalars K₀) :=
    IsModuleTopology.continuous_of_linearMap (f.symm.restrictScalars K₀).toLinearMap
  change valuation L₂ (f x) ≤ 1 ↔ valuation L₁ x ≤ 1
  refine ⟨fun hx => ?_, preserves_integers_of_continuous_symm f.toRingEquiv hf'⟩
  have h := preserves_integers_of_continuous_symm f.symm.toRingEquiv hf hx
  change valuation L₁ (f.symm (f x)) ≤ 1 at h
  rwa [f.symm_apply_apply] at h

/-- The integer-ring isomorphism induced by `f`. -/
def integerEquiv : T₁.Integers ≃+* T₂.Integers where
  toFun x := ⟨f x, (map_mem_integers_iff T₁ T₂ K f x).mpr x.property⟩
  invFun y := ⟨f.symm y, by
    rw [← map_mem_integers_iff T₁ T₂ K f, f.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul f (x : L₁) (y : L₁))
  map_add' x y := Subtype.ext (map_add f (x : L₁) (y : L₁))

end FieldEquiv

section AmbientUpperGroup

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
  (Ω : Type uΩ₁) [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ vle a b)

private instance finiteGalois_finiteDimensional
    (M : FiniteGaloisIntermediateField K Ω) : FiniteDimensional K₀ M :=
  FiniteDimensional.trans K₀ K M

/-- The same restriction intersection as `absoluteUpperRamificationGroup`,
formed in any ambient extension of the base. -/
def upperGroupIn (v : ℝ) : Subgroup Gal(Ω/K) :=
  ⨅ M : FiniteGaloisIntermediateField K Ω,
    (canonicalUpperRamificationGroup K₀ M hbase K v).comap
      (absoluteFiniteRestriction K Ω M).toMonoidHom

/-- Membership is the upper-group condition at each finite Galois subfield. -/
theorem mem_upperGroupIn_iff (v : ℝ) (σ : Gal(Ω/K)) :
    σ ∈ upperGroupIn K₀ K Ω hbase v ↔ ∀ M : FiniteGaloisIntermediateField K Ω,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ ∈
        canonicalUpperRamificationGroup K₀ M hbase K v := by
  simp only [upperGroupIn, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

end AmbientUpperGroup

section Comap

variable (K : Type uK) [Field K]
  {Ω₁ : Type uΩ₁} [Field Ω₁] [Algebra K Ω₁]
  {Ω₂ : Type uΩ₂} [Field Ω₂] [Algebra K Ω₂]

/-- The preimage of a finite Galois subfield under an ambient isomorphism. -/
def comapFiniteGalois (e : Ω₁ ≃ₐ[K] Ω₂) (M : FiniteGaloisIntermediateField K Ω₂) :
    FiniteGaloisIntermediateField K Ω₁ where
  toIntermediateField := M.toIntermediateField.map (e.symm : Ω₂ →ₐ[K] Ω₁)
  finiteDimensional := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K] Ω₁)).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K] Ω₁))

/-- The restriction of the ambient isomorphism to the preimage field. -/
def comapFiniteGaloisEquiv (e : Ω₁ ≃ₐ[K] Ω₂) (M : FiniteGaloisIntermediateField K Ω₂) :
    comapFiniteGalois K e M ≃ₐ[K] M :=
  (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K] Ω₁)).symm

/-- The restricted isomorphism applies the ambient isomorphism on elements. -/
theorem comapFiniteGaloisEquiv_coe (e : Ω₁ ≃ₐ[K] Ω₂)
    (M : FiniteGaloisIntermediateField K Ω₂) (z : comapFiniteGalois K e M) :
    ((comapFiniteGaloisEquiv K e M z : M) : Ω₂) = e (z : Ω₁) := by
  have he : (IntermediateField.equivMap M.toIntermediateField (e.symm : Ω₂ →ₐ[K] Ω₁)
      (comapFiniteGaloisEquiv K e M z) : Ω₁) = (z : Ω₁) :=
    congrArg Subtype.val ((IntermediateField.equivMap M.toIntermediateField
      (e.symm : Ω₂ →ₐ[K] Ω₁)).apply_symm_apply z)
  rw [IntermediateField.coe_equivMap_apply] at he
  rw [← he]
  simp

end Comap
end Langlands.Ramification.Local
