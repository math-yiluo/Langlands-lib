import Langlands.LinearAlgebra.GMFamilyAffineBases
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Gram volumes for two subspaces -/

noncomputable section

open Classical
open scoped RealInnerProductSpace Matrix

namespace Langlands.GMFamily

variable {D E : Type*} [AddCommGroup D] [Module ℝ D] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem gramVolume_map_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ D) (f : D →ₗ[ℝ] E) (v : ι → D) :
    gramVolume (f ∘ v) = gramVolume (f ∘ b) * |(b.toMatrix v).det| := by
  let C := b.toMatrix v
  have hv (i : ι) : f (v i) = ∑ k, C k i • f (b k) := by
    simpa only [C, Module.Basis.toMatrix_apply, map_sum, map_smul] using
      congrArg f (b.sum_repr (v i)).symm
  have hG : Matrix.gram ℝ (f ∘ v) = Cᵀ * (Matrix.gram ℝ (f ∘ b) * C) := by
    ext i j
    simp only [Matrix.gram_apply, Function.comp_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.mul_sum]
    rw [hv i, hv j, sum_inner]
    apply Finset.sum_congr rfl
    intro k _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring
  change Real.sqrt (Matrix.gram ℝ (f ∘ v)).det = _
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show C.det * ((Matrix.gram ℝ (f ∘ b)).det * C.det) =
    (Matrix.gram ℝ (f ∘ b)).det * C.det ^ 2 by ring,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

variable [FiniteDimensional ℝ E]

private def addSubspaces (U W : Submodule ℝ E) : U × W →ₗ[ℝ] E := U.subtype.coprod W.subtype

omit [FiniteDimensional ℝ E] in
private theorem addSubspaces_prod_basis {ι κ : Type*} {U W : Submodule ℝ E}
    (b : Module.Basis ι ℝ U) (c : Module.Basis κ ℝ W) :
    addSubspaces U W ∘ (b.prod c) =
      Sum.elim (fun i => ((b i : U) : E)) (fun j => ((c j : W) : E)) := by
  funext i
  cases i <;> simp [addSubspaces, LinearMap.coprod_apply]

/-- The volume of the combined family factors through the two internal volumes and
Arthur's Euclidean measure factor. -/
theorem gramVolume_sum_eq_measureFactor {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U W V : Submodule ℝ E} (b : Module.Basis ι ℝ U) (c : Module.Basis κ ℝ W)
    (hdim : Module.finrank ℝ U + Module.finrank ℝ W = Module.finrank ℝ V) :
    gramVolume (Sum.elim (fun i => ((b i : U) : E)) (fun j => ((c j : W) : E))) =
      measureFactor U W V * gramVolume b * gramVolume c := by
  let o := stdOrthonormalBasis ℝ U
  let p := stdOrthonormalBasis ℝ W
  let e : Fin (Module.finrank ℝ U) ≃ ι := Fintype.equivOfCardEq (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b])
  let g : Fin (Module.finrank ℝ W) ≃ κ := Fintype.equivOfCardEq (by rw [Fintype.card_fin, Module.finrank_eq_card_basis c])
  let bo := (o.reindex e).toBasis
  let cp := (p.reindex g).toBasis
  have hvol : gramVolume (addSubspaces U W ∘ (bo.prod cp)) = measureFactor U W V := by
    rw [addSubspaces_prod_basis, measureFactor, ite_eq_left hdim]
    rw [← gramVolume_reindex (Equiv.sumCongr e g) _]
    congr 1
    funext i
    cases i <;> simp [bo, cp, o, p]
  have hmat : (bo.prod cp).toMatrix (b.prod c) =
      Matrix.fromBlocks (bo.toMatrix b) 0 0 (cp.toMatrix c) := by
    ext i j
    cases i <;> cases j <;> simp [Module.Basis.toMatrix_apply]
  have hdet : (Matrix.fromBlocks (bo.toMatrix b) 0 0 (cp.toMatrix c)).det =
      (bo.toMatrix b).det * (cp.toMatrix c).det := by
    exact Matrix.det_fromBlocks_zero₂₁ (bo.toMatrix b) 0 (cp.toMatrix c)
  rw [← addSubspaces_prod_basis, gramVolume_map_basis (bo.prod cp), hvol, hmat]
  calc
    _ = measureFactor U W V * |(bo.toMatrix b).det * (cp.toMatrix c).det| := by
      congr 2
      convert hdet using 1
      congr
    _ = _ := by
      rw [abs_mul, ← mul_assoc, gramVolume_eq_abs_det_toMatrix (o.reindex e), gramVolume_eq_abs_det_toMatrix (p.reindex g)]

/-- For two subspaces in `V`, the concatenation of their orthonormal bases is a basis
of `V` precisely when the measure factor is nonzero. -/
theorem measureFactor_ne_zero_iff {U W V : Submodule ℝ E} (hU : U ≤ V) (hW : W ≤ V) :
    measureFactor U W V ≠ 0 ↔
      Disjoint U W ∧ U ⊔ W = V := by
  let b := stdOrthonormalBasis ℝ U
  let c := stdOrthonormalBasis ℝ W
  let f := addSubspaces U W
  have hker : Function.Injective f ↔ Disjoint U W := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    constructor
    · intro hf
      apply Submodule.disjoint_def.mpr
      intro x hxU hxW
      have h := hf (⟨x, hxU⟩, -⟨x, hxW⟩) (by simp [f, addSubspaces, LinearMap.coprod_apply])
      exact congrArg (fun y : U × W => (y.1 : E)) h
    · intro hd x hx
      have hx' : (x.1 : E) + (x.2 : E) = 0 := hx
      have he : (x.1 : E) = -(x.2 : E) := eq_neg_of_add_eq_zero_left hx'
      have h0 : (x.1 : E) = 0 := (Submodule.disjoint_def.mp hd) _ x.1.property
        (he ▸ W.neg_mem x.2.property)
      apply Prod.ext
      · exact Subtype.ext h0
      · exact Subtype.ext (by simpa [h0] using hx')
  have hspan : Submodule.span ℝ (Set.range (f ∘ b.toBasis.prod c.toBasis)) = U ⊔ W := by
    rw [Set.range_comp, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top]
    simp only [f, addSubspaces, LinearMap.range_coprod, Submodule.range_subtype]
  have hli : LinearIndependent ℝ (f ∘ b.toBasis.prod c.toBasis) ↔ Function.Injective f := by
    constructor
    · intro h
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      let d := b.toBasis.prod c.toBasis
      have hs : ∑ i, d.repr x i • (f ∘ d) i = 0 := by
        simpa only [Function.comp_apply, ← map_smul, ← map_sum, d.sum_repr] using hx
      have hzero := Fintype.linearIndependent_iff.mp h _ hs
      apply d.repr.injective
      ext i
      simpa only [map_zero, Finsupp.zero_apply] using hzero i
    · intro h
      exact (b.toBasis.prod c.toBasis).linearIndependent.map' f (LinearMap.ker_eq_bot.mpr h)
  change (if Module.finrank ℝ U + Module.finrank ℝ W = Module.finrank ℝ V then
    gramVolume (Sum.elim (fun i => ((b.toBasis i : U) : E)) (fun j => ((c.toBasis j : W) : E)))
    else 0) ≠ 0 ↔ _
  rw [← addSubspaces_prod_basis b.toBasis c.toBasis]
  change (if _ then gramVolume (f ∘ b.toBasis.prod c.toBasis) else 0) ≠ 0 ↔ _
  constructor
  · by_cases h : Module.finrank ℝ U + Module.finrank ℝ W = Module.finrank ℝ V
    · rw [ite_eq_left h, gramVolume_ne_zero_iff]
      intro hl
      refine ⟨hker.mp (hli.mp hl), ?_⟩
      have hfint := finrank_span_eq_card hl
      rw [hspan, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, h] at hfint
      exact Submodule.eq_of_le_of_finrank_le (sup_le hU hW) hfint.ge
    · simp [h]
  · rintro ⟨hd, hs⟩
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hs, hd.eq_bot, finrank_bot, add_zero] at h
    rw [ite_eq_left h.symm, gramVolume_ne_zero_iff]
    exact hli.mpr (hker.mpr hd)

end Langlands.GMFamily
