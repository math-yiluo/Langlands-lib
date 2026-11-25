import Langlands.LocalFactor.Ramification.Wintenberger.Absolute
import FontaineWintenberger.APF.Elementary.Basic
import FontaineWintenberger.APF.Herbrand
import FontaineWintenberger.Ramification.Infinite.Restriction
import FontaineWintenberger.APF.Tower.Criterion

/-!
# Arithmetically profinite extensions in the Library's filtrations

The notions of Wintenberger §1 in the FontaineWintenberger library (`apfSubgroup`, `IsAPF`,
`IsElementary`, `apfIndex`, `apfPsi`) are defined from the absolute upper filtration of a field
in its separable closure `SeparableClosure K` and from fixing subgroups. Through the equality of
the absolute filtrations of the two libraries, each of them is a statement about the Library's
filtration `Local.absoluteUpperRamificationGroup K₀ K Ω hbase` in any separable closure `Ω`.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe u₀ uK uΩ uΩ' uL

section FixingSubgroup

variable {B : Type*} {Ω₁ Ω₂ : Type*} [Field B] [Field Ω₁] [Field Ω₂] [Algebra B Ω₁] [Algebra B Ω₂]

/-- Conjugation by an isomorphism of extensions carries the fixing subgroup of an intermediate
field to the fixing subgroup of its image. -/
theorem fixingSubgroup_map_autCongr (e : Ω₁ ≃ₐ[B] Ω₂) (S : IntermediateField B Ω₁) :
    S.fixingSubgroup.map e.autCongr.toMonoidHom = (S.map e.toAlgHom).fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, hx, rfl⟩
    change e (τ (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hτ x hx]
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine ⟨e.autCongr.symm σ, ?_, e.autCongr.apply_symm_apply σ⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change e.symm (σ (e x)) = x
    rw [hσ (e x) ⟨x, hx, rfl⟩, e.symm_apply_apply]

open scoped Topology in
/-- Conjugation by an isomorphism of extensions is continuous for the Krull topologies. -/
theorem continuous_autCongr (e : Ω₁ ≃ₐ[B] Ω₂) : Continuous e.autCongr := by
  apply continuous_of_continuousAt_one e.autCongr
  change Filter.Tendsto e.autCongr (𝓝 1) (𝓝 (e.autCongr 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff B Ω₂ s).mp hs
  have : FiniteDimensional B D := hD
  have hC : FiniteDimensional B (D.map e.symm.toAlgHom) :=
    (IntermediateField.intermediateFieldMap e.symm D).toLinearEquiv.finiteDimensional
  apply (krullTopology_mem_nhds_one_iff B Ω₁ _).mpr
  refine ⟨D.map e.symm.toAlgHom, hC, fun σ hσ => hDs ?_⟩
  have h : e.autCongr σ ∈ ((D.map e.symm.toAlgHom).map e.toAlgHom).fixingSubgroup := by
    rw [← fixingSubgroup_map_autCongr]
    exact ⟨σ, hσ, rfl⟩
  rwa [IntermediateField.map_map, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id B Ω₂ from
    AlgHom.ext e.apply_symm_apply, IntermediateField.map_id] at h

/-- Conjugation by an isomorphism of extensions, as a homeomorphism of Krull topologies. -/
def autCongrHomeomorph (e : Ω₁ ≃ₐ[B] Ω₂) : (Ω₁ ≃ₐ[B] Ω₁) ≃ₜ (Ω₂ ≃ₐ[B] Ω₂) where
  toEquiv := e.autCongr.toEquiv
  continuous_toFun := continuous_autCongr e
  continuous_invFun := continuous_autCongr e.symm

end FixingSubgroup

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀] [CompleteSpace K₀]
  [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

section ClosureChange

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K]
  [FontaineWintenberger.IsCompleteDiscreteValuedField K] [FiniteDimensional K₀ K]
  {Ω₁ : Type uΩ} [Field Ω₁] [Algebra K Ω₁] [Algebra K₀ Ω₁] [IsScalarTower K₀ K Ω₁]
  [IsSepClosure K Ω₁]
  {Ω₂ : Type uΩ'} [Field Ω₂] [Algebra K Ω₂] [Algebra K₀ Ω₂] [IsScalarTower K₀ K Ω₂]
  [IsSepClosure K Ω₂]

/-- The Library's absolute upper filtration does not depend on the separable closure: an
isomorphism of separable closures carries one filtration onto the other by conjugation. -/
theorem absoluteUpperRamificationGroup_map_autCongr (e : Ω₁ ≃ₐ[K] Ω₂) {v : ℝ} (hv : -1 ≤ v) :
    (Local.absoluteUpperRamificationGroup K₀ K Ω₁ hbase v).map e.autCongr.toMonoidHom =
      Local.absoluteUpperRamificationGroup K₀ K Ω₂ hbase v := by
  rw [← upperRamificationGroupInfinite_eq_absolute K₀ hbase K Ω₁,
    ← upperRamificationGroupInfinite_eq_absolute K₀ hbase K Ω₂]
  exact FontaineWintenberger.upperRamificationGroupInfinite_map_autCongr K e hv

/-- The APF subgroup of the image of an embedding into `SeparableClosure K`, computed in any
other separable closure `Ω` through the Library's filtration. -/
theorem apfSubgroup_eq_map (e : Ω₁ ≃ₐ[K] SeparableClosure K) (S : IntermediateField K Ω₁)
    {v : ℝ} (hv : -1 ≤ v) :
    FontaineWintenberger.apfSubgroup K (S.map e.toAlgHom) v =
      (S.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ K Ω₁ hbase v).map
        e.autCongr.toMonoidHom := by
  rw [Subgroup.map_sup, fixingSubgroup_map_autCongr,
    absoluteUpperRamificationGroup_map_autCongr K₀ hbase K e hv,
    ← upperRamificationGroupInfinite_eq_absolute K₀ hbase K (SeparableClosure K)]
  rfl

end ClosureChange

section Elementary

variable (B : Type uK) [NontriviallyNormedField B] [NormedAlgebra K₀ B]
  [FontaineWintenberger.IsCompleteDiscreteValuedField B] [FiniteDimensional K₀ B]
  (Ω : Type uΩ) [Field Ω] [Algebra B Ω] [Algebra K₀ Ω] [IsScalarTower K₀ B Ω] [IsSepClosure B Ω]
  (L : Type uL) [Field L] [Algebra B L] [FiniteDimensional B L] [Algebra.IsSeparable B L]

/-- **An elementary extension in the Library's filtration is elementary in the sense of
Wintenberger 1.3.1.** If, for one embedding `f` of `L` into a separable closure `Ω`, the fixing
subgroup of the image and the Library's upper group at `i` generate the whole Galois group, and
every upper group beyond `i` fixes the image, then `L/B` is elementary of level `i`. -/
theorem isElementary_of_absoluteUpper (f : L →ₐ[B] Ω) {i : ℝ} (hi : 0 < i)
    (htop : f.fieldRange.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ B Ω hbase i = ⊤)
    (hfix : ∀ x : ℝ, i < x →
      Local.absoluteUpperRamificationGroup K₀ B Ω hbase x ≤ f.fieldRange.fixingSubgroup) :
    FontaineWintenberger.IsElementary B L i := by
  let e : Ω ≃ₐ[B] SeparableClosure B := IsSepClosure.equiv B Ω (SeparableClosure B)
  let j : L →ₐ[B] SeparableClosure B := e.toAlgHom.comp f
  have hj : j.fieldRange = f.fieldRange.map e.toAlgHom := by
    rw [AlgHom.map_fieldRange]
  refine FontaineWintenberger.IsElementary.of_embedding j hi ?_ fun x hx => ?_
  · rw [hj, apfSubgroup_eq_map K₀ hbase B e _ (by linarith), htop]
    exact Subgroup.map_top_of_surjective _ e.autCongr.surjective
  · rw [hj, apfSubgroup_eq_map K₀ hbase B e _ (by linarith), sup_eq_left.mpr (hfix x hx),
      fixingSubgroup_map_autCongr]

end Elementary

section NormedTower

variable (K₀ : Type*) [NontriviallyNormedField K₀] (K : Type*) [NontriviallyNormedField K]
  [NormedAlgebra K₀ K] [IsUltrametricDist K] [CompleteSpace K]
  (B : Type*) [Field B] [Algebra K B] [Algebra K₀ B] [IsScalarTower K₀ K B]
  [Algebra.IsAlgebraic K B]

/-- An algebraic extension of a normed extension `K` of `K₀`, with the spectral norm over `K`,
is a normed `K₀`-algebra for its given algebra structure. -/
@[instance_reducible]
def spectralNormedAlgebraOfTower :
    letI := spectralNorm.nontriviallyNormedField K B
    NormedAlgebra K₀ B :=
  letI := spectralNorm.nontriviallyNormedField K B
  letI := spectralNorm.normedAlgebra K B
  { (inferInstance : Algebra K₀ B) with
    norm_smul_le := fun r x => by
      rw [Algebra.smul_def, norm_mul, IsScalarTower.algebraMap_apply K₀ K B, norm_algebraMap',
        norm_algebraMap'] }

end NormedTower

section ElementaryStep

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K]
  [FontaineWintenberger.IsCompleteDiscreteValuedField K]

/-- **An elementary step in the Library's filtration of its base is an elementary step of the
FontaineWintenberger library.** For finite subfields `E ≤ E'` of `SeparableClosure K`, if for one
embedding `f` of `E'` over `E` into a separable closure `Ω` of `E` the Library's filtration of `E`
(over the base `K₀`) satisfies the two conditions of Wintenberger 1.3.1 at level `i`, then the
step is elementary of level `i` for the spectral norm of `E` over `K`. -/
theorem isElementaryStep_of_absoluteUpper
    (E E' : FontaineWintenberger.FiniteIntermediateField K (SeparableClosure K)) (hEE' : E ≤ E')
    [FiniteDimensional K₀ E.val] (Ω : Type uΩ) [Field Ω] [Algebra E.val Ω] [Algebra K₀ Ω] [IsScalarTower K₀ E.val Ω]
    [IsSepClosure E.val Ω]
    (f : IntermediateField.extendScalars hEE' →ₐ[E.val] Ω) {i : ℝ} (hi : 0 < i)
    (htop : f.fieldRange.fixingSubgroup ⊔
      Local.absoluteUpperRamificationGroup K₀ E.val Ω hbase i = ⊤)
    (hfix : ∀ x : ℝ, i < x →
      Local.absoluteUpperRamificationGroup K₀ E.val Ω hbase x ≤ f.fieldRange.fixingSubgroup) :
    FontaineWintenberger.IsElementaryStep K E E' hEE' i := by
  have : FiniteDimensional K (IntermediateField.extendScalars hEE') := E'.2
  have : FiniteDimensional E.val (IntermediateField.extendScalars hEE') :=
    Module.Finite.of_restrictScalars_finite K E.val (IntermediateField.extendScalars hEE')
  unfold FontaineWintenberger.IsElementaryStep
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  have : IsUltrametricDist E.val :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  have := spectralNorm.completeSpace K E.val
  have := FontaineWintenberger.normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := spectralNormedAlgebraOfTower K₀ K E.val
  exact isElementary_of_absoluteUpper K₀ hbase E.val Ω (IntermediateField.extendScalars hEE') f hi
    htop hfix

end ElementaryStep

section Dictionary

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K]
  [FontaineWintenberger.IsCompleteDiscreteValuedField K] [FiniteDimensional K₀ K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω] [IsSepClosure K Ω]
  (L : Type uL) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- **Arithmetic profiniteness in the Library's filtration.** `L/K` is APF if and only if, for an
embedding `i` of `L` into a separable closure `Ω`, the fixing subgroup of its image and every
upper group `G_K^u`, `u ≥ -1`, of the Library generate an open subgroup. -/
theorem isAPF_iff_isOpen (i : L →ₐ[K] Ω) :
    FontaineWintenberger.IsAPF K L ↔ ∀ u : ℝ, -1 ≤ u →
      IsOpen ((i.fieldRange.fixingSubgroup ⊔
        Local.absoluteUpperRamificationGroup K₀ K Ω hbase u : Subgroup (Ω ≃ₐ[K] Ω)) :
          Set (Ω ≃ₐ[K] Ω)) := by
  let e : Ω ≃ₐ[K] SeparableClosure K := IsSepClosure.equiv K Ω (SeparableClosure K)
  let j : L →ₐ[K] SeparableClosure K := e.toAlgHom.comp i
  have hj : j.fieldRange = i.fieldRange.map e.toAlgHom := by
    rw [AlgHom.map_fieldRange]
  rw [FontaineWintenberger.isAPF_iff_embedding K L j, FontaineWintenberger.isAPFSubextension_iff]
  refine forall₂_congr fun u hu => ?_
  rw [hj, apfSubgroup_eq_map K₀ hbase K e _ hu, Subgroup.coe_map]
  exact (autCongrHomeomorph e).isOpen_image

/-- **The index of Wintenberger 1.2.1 in the Library's filtration.** For `u ≥ 0` and an embedding
`i` of `L` into a separable closure `Ω`, with `G^v` the Library's upper groups,
`apfIndex K L u = ((G_L ⊓ G^0) ⊔ G^u : G^0)`. -/
theorem apfIndex_eq_relIndex (i : L →ₐ[K] Ω) {u : ℝ} (hu : 0 ≤ u) :
    FontaineWintenberger.apfIndex K L u =
      ((i.fieldRange.fixingSubgroup ⊓ Local.absoluteUpperRamificationGroup K₀ K Ω hbase 0) ⊔
        Local.absoluteUpperRamificationGroup K₀ K Ω hbase u).relIndex
        (Local.absoluteUpperRamificationGroup K₀ K Ω hbase 0) := by
  let e : Ω ≃ₐ[K] SeparableClosure K := IsSepClosure.equiv K Ω (SeparableClosure K)
  let j : L →ₐ[K] SeparableClosure K := e.toAlgHom.comp i
  have hj : j.fieldRange = i.fieldRange.map e.toAlgHom := by
    rw [AlgHom.map_fieldRange]
  have hG : ∀ v : ℝ, -1 ≤ v → FontaineWintenberger.absoluteUpperRamificationGroup K v =
      (Local.absoluteUpperRamificationGroup K₀ K Ω hbase v).map e.autCongr.toMonoidHom := by
    intro v hv
    rw [absoluteUpperRamificationGroup_map_autCongr K₀ hbase K e hv,
      ← upperRamificationGroupInfinite_eq_absolute K₀ hbase K (SeparableClosure K)]
  rw [FontaineWintenberger.apfIndex_eq_embedding K L j, FontaineWintenberger.apfInertiaIndex,
    FontaineWintenberger.apfInertiaSubgroup, hj, ← fixingSubgroup_map_autCongr,
    hG 0 (by norm_num), hG u (by linarith),
    ← Subgroup.map_inf_eq (f := e.autCongr.toMonoidHom) _ _ e.autCongr.injective,
    ← Subgroup.map_sup,
    Subgroup.relIndex_map_map_of_injective _ _ e.autCongr.injective]

/-- If the fixing subgroup of `L` and the Library's upper group at `μ ≥ 0` generate the whole
Galois group, then Wintenberger's `ψ_{L/K}` is the identity up to `μ`. -/
theorem apfPsi_eq_self_of_sup_eq_top (i : L →ₐ[K] Ω) {μ : ℝ}
    (htop : i.fieldRange.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ K Ω hbase μ = ⊤)
    {u : ℝ} (hu : u ≤ μ) :
    FontaineWintenberger.apfPsi K L u = u := by
  have hindex : ∀ v : ℝ, 0 ≤ v → v ≤ μ → FontaineWintenberger.apfIndex K L v = 1 := by
    intro v hv hvμ
    rw [apfIndex_eq_relIndex K₀ hbase K Ω L i hv, Subgroup.relIndex_eq_one]
    have hmono := Local.absoluteUpperRamificationGroup_antitone K₀ K Ω hbase
    have htop' : i.fieldRange.fixingSubgroup ⊔
        Local.absoluteUpperRamificationGroup K₀ K Ω hbase v = ⊤ :=
      top_unique (htop ▸ sup_le_sup_left (hmono hvμ) _)
    intro σ hσ
    obtain ⟨τ, hτ, δ, hδ, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
      (htop' ▸ (Subgroup.mem_top σ))
    have hδ0 : δ ∈ Local.absoluteUpperRamificationGroup K₀ K Ω hbase 0 := hmono hv hδ
    have hτ0 : τ ∈ Local.absoluteUpperRamificationGroup K₀ K Ω hbase 0 := by
      simpa using Subgroup.mul_mem _ hσ (Subgroup.inv_mem _ hδ0)
    exact Subgroup.mul_mem_sup ⟨hτ, hτ0⟩ hδ
  rcases le_or_gt u 0 with hu0 | hu0
  · exact FontaineWintenberger.apfPsi_of_nonpos K L hu0
  · have h : FontaineWintenberger.apfPsi K L u = ∫ _ in (0 : ℝ)..u, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le hu0.le]
      intro v hv
      change (FontaineWintenberger.apfIndex K L (max v 0) : ℝ) = 1
      rw [max_eq_left hv.1, hindex v hv.1 (hv.2.trans hu), Nat.cast_one]
    rw [h, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

end Dictionary

end Langlands.Ramification.Wintenberger
