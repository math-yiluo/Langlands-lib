import Langlands.LinearAlgebra.GMFamilyGramVolume
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Volumes and transversality for Levi descent -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem gramVolume_join_orthogonalProjection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U) (w : κ → E) :
    gramVolume (Sum.elim (fun i => (b i : E)) w) =
      gramVolume (fun j => Uᗮ.starProjection (w j)) := by
  let B : Matrix ι κ ℝ := Matrix.of fun i j => ⟪(b i : E), w j⟫
  let C : Matrix κ ι ℝ := Matrix.of fun i j => ⟪w i, (b j : E)⟫
  have hb : Matrix.gram ℝ (fun i => (b i : E)) = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal
  have hblocks : Matrix.gram ℝ (Sum.elim (fun i => (b i : E)) w) =
      Matrix.fromBlocks 1 B C (Matrix.gram ℝ w) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg (fun m : Matrix ι ι ℝ => m i j) hb
    · rfl
    · rfl
    · rfl
  have hproj (x y : E) :
      ⟪x, y⟫ - ⟪U.starProjection x, U.starProjection y⟫ =
        ⟪Uᗮ.starProjection x, Uᗮ.starProjection y⟫ := by
    have hxy := U.starProjection_inner_eq_zero x (U.starProjection y) (U.starProjection_apply_mem y)
    have hyx := U.starProjection_inner_eq_zero y (U.starProjection x) (U.starProjection_apply_mem x)
    rw [inner_sub_left, sub_eq_zero] at hxy hyx
    rw [real_inner_comm (U.starProjection x) y,
      real_inner_comm (U.starProjection x) (U.starProjection y)] at hyx
    simp only [starProjection_orthogonal_val, inner_sub_left, inner_sub_right]
    rw [hxy, hyx]
    ring
  have hcompl : Matrix.gram ℝ w - C * B =
      Matrix.gram ℝ (fun j => Uᗮ.starProjection (w j)) := by
    ext i j
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto (w i))
      (U.orthogonalProjectionOnto (w j))
    have h' : (C * B) i j = ⟪U.starProjection (w i), U.starProjection (w j)⟫ := by
      change (C * B) i j = ⟪U.orthogonalProjectionOnto (w i), U.orthogonalProjectionOnto (w j)⟫
      simpa only [C, B, Matrix.mul_apply, Matrix.of_apply,
        inner_orthogonalProjectionOnto_eq_of_mem_left,
        inner_orthogonalProjectionOnto_eq_of_mem_right] using h
    change ⟪w i, w j⟫ - (C * B) i j = _
    rw [h', hproj]
    rfl
  have hdet := Matrix.det_fromBlocks_one₁₁ B C (Matrix.gram ℝ w)
  rw [hcompl, ← hblocks] at hdet
  unfold gramVolume
  apply congrArg Real.sqrt
  convert hdet using 1
  · exact congrArg (fun d => @Matrix.det (ι ⊕ κ) d _ ℝ _
      (Matrix.gram ℝ (Sum.elim (fun i => (b i : E)) w))) (Subsingleton.elim _ _)
  · rfl

private theorem gramVolume_linearMap_orthonormalBasis {ι U V : Type*} [Fintype ι]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis ι ℝ U) (f : U →ₗ[ℝ] V) :
    gramVolume (fun i => f (b i)) = f.normDet := by
  change Real.sqrt (Matrix.gram ℝ _).det = _
  have h := f.normDet_sq_eq_det_gram b
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [← h, Real.sqrt_sq f.normDet_nonneg]

/-- Orthogonal projection from the transverse Levi directions to the coarse noncentral space. -/
def descentProjection (a z a₁ L : Submodule ℝ E) :
    (a₁ ⊓ Lᗮ : Submodule ℝ E) →ₗ[ℝ] (a ⊓ zᗮ : Submodule ℝ E) :=
  (a ⊓ zᗮ : Submodule ℝ E).orthogonalProjectionOnto.toLinearMap.comp (a₁ ⊓ Lᗮ).subtype

private theorem starProjection_descent_eq {a z a₁ : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) {x : E} (hx : x ∈ a₁ ⊓ zᗮ) :
    (a₁ ⊓ aᗮ : Submodule ℝ E)ᗮ.starProjection x = (a ⊓ zᗮ : Submodule ℝ E).starProjection x := by
  let y := a.starProjection x
  have hya : y ∈ a := a.starProjection_apply_mem x
  have hyz : y ∈ zᗮ := by
    intro w hw
    have h := a.starProjection_inner_eq_zero x w (hza hw)
    rw [inner_sub_left, sub_eq_zero, real_inner_comm, hx.2 w hw] at h
    exact (inner_eq_zero_symm.mp h.symm)
  have ho : x - y ∈ aᗮ := a.sub_starProjection_mem_orthogonal x
  have hu : x - y ∈ a₁ ⊓ aᗮ := ⟨a₁.sub_mem hx.1 (haa₁ hya), ho⟩
  have hA : y ∈ a ⊓ zᗮ := ⟨hya, hyz⟩
  have hU : y ∈ (a₁ ⊓ aᗮ : Submodule ℝ E)ᗮ :=
    orthogonal_le inf_le_right (a.le_orthogonal_orthogonal hya)
  exact (eq_starProjection_of_mem_orthogonal hU
    ((a₁ ⊓ aᗮ : Submodule ℝ E).le_orthogonal_orthogonal hu)).trans
      (eq_starProjection_of_mem_orthogonal hA (orthogonal_le inf_le_left ho)).symm

private theorem descent_dimension {a z a₁ : Submodule ℝ E} (hza : z ≤ a) (haa₁ : a ≤ a₁) :
    finrank ℝ (a₁ ⊓ aᗮ : Submodule ℝ E) + finrank ℝ (a ⊓ zᗮ : Submodule ℝ E) =
      finrank ℝ (a₁ ⊓ zᗮ : Submodule ℝ E) := by
  have ha := finrank_add_inf_finrank_orthogonal hza
  have hb := finrank_add_inf_finrank_orthogonal (hza.trans haa₁)
  have hc := finrank_add_inf_finrank_orthogonal haa₁
  rw [inf_comm] at ha hb hc
  omega

private theorem dDescent_eq_normDet {a z a₁ L : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) (hzL : z ≤ L)
    (hdim : finrank ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) = finrank ℝ (a ⊓ zᗮ : Submodule ℝ E)) :
    dDescent a z a₁ L = (descentProjection a z a₁ L).normDet := by
  let W : Submodule ℝ E := a₁ ⊓ Lᗮ
  let U : Submodule ℝ E := a₁ ⊓ aᗮ
  let b := stdOrthonormalBasis ℝ W
  have ht : finrank ℝ U + finrank ℝ W = finrank ℝ (a₁ ⊓ zᗮ : Submodule ℝ E) := by
    rw [hdim, descent_dimension hza haa₁]
  unfold dDescent measureFactor
  rw [ite_eq_left ht, gramVolume_join_orthogonalProjection]
  have hproj (i) : Uᗮ.starProjection (b i : E) =
      (descentProjection a z a₁ L (b i) : E) := starProjection_descent_eq hza haa₁
        ⟨(b i).prop.1, orthogonal_le hzL (b i).prop.2⟩
  change gramVolume (fun i => Uᗮ.starProjection (b i : E)) = _
  rw [show (fun i => Uᗮ.starProjection (b i : E)) =
    (fun i => (descentProjection a z a₁ L (b i) : E)) from funext hproj,
    gramVolume_subtype, gramVolume_linearMap_orthonormalBasis b]

/-- The nonzero descent coefficients correspond exactly to bijective projected maps. -/
theorem dDescent_ne_zero_iff {a z a₁ L : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) (hzL : z ≤ L) :
    dDescent a z a₁ L ≠ 0 ↔ Function.Bijective (descentProjection a z a₁ L) := by
  let f := descentProjection a z a₁ L
  change _ ↔ Function.Bijective f
  by_cases hd : finrank ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) = finrank ℝ (a ⊓ zᗮ : Submodule ℝ E)
  · rw [dDescent_eq_normDet hza haa₁ hzL hd, ne_eq, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
      not_ne_iff, LinearMap.ker_eq_bot]
    exact ⟨fun hi => ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩,
      fun hb => hb.1⟩
  have hneq : ¬ finrank ℝ (a₁ ⊓ aᗮ : Submodule ℝ E) + finrank ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E) =
      finrank ℝ (a₁ ⊓ zᗮ : Submodule ℝ E) := by
    have hs := descent_dimension hza haa₁
    omega
  rw [dDescent, measureFactor, ite_eq_right hneq]
  exact ⟨fun hn => (hn rfl).elim, fun hb => (hd (LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hb))).elim⟩

/-- The descent coefficient converts the volume of a basis of the Levi normal space to the
    volume of its projected family. -/
theorem dDescent_mul_gramVolume {ι : Type*} [Fintype ι] {a z a₁ L : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) (hzL : z ≤ L)
    (hd : dDescent a z a₁ L ≠ 0) (b : Basis ι ℝ (a₁ ⊓ Lᗮ : Submodule ℝ E)) :
    dDescent a z a₁ L * gramVolume (fun i => (b i : E)) =
      gramVolume (fun i => descentProjection a z a₁ L (b i)) := by
  have hbij := (dDescent_ne_zero_iff hza haa₁ hzL).mp hd
  let W : Submodule ℝ E := a₁ ⊓ Lᗮ
  let f := descentProjection a z a₁ L
  let q : OrthonormalBasis ι ℝ W := (stdOrthonormalBasis ℝ W).reindex
    (Fintype.equivOfCardEq (by simp [W, finrank_eq_card_basis b]))
  let g : W →ₗ[ℝ] W := q.toBasis.constr ℝ b
  have hg (i : ι) : g (q i) = b i := q.toBasis.constr_basis (S := ℝ) b i
  have hgvol : gramVolume (fun i => (b i : E)) = g.normDet := by
    rw [gramVolume_subtype]
    simpa only [hg] using gramVolume_linearMap_orthonormalBasis q g
  have hfgvol : gramVolume (fun i => f (b i)) = (f.comp g).normDet := by
    simpa only [LinearMap.comp_apply, hg] using gramVolume_linearMap_orthonormalBasis q (f.comp g)
  rw [dDescent_eq_normDet hza haa₁ hzL (LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hbij)),
    hgvol, hfgvol, LinearMap.normDet_comp_of_finrank_eq g f rfl]

/-- Represent a real linear functional by inner product with a vector. -/
theorem exists_inner_eq_dual (f : Module.Dual ℝ E) :
    ∃ x : E, ∀ y : E, ⟪y, x⟫ = f y := by
  let e := InnerProductSpace.toDual ℝ E
  let x := e.symm f.toContinuousLinearMap
  refine ⟨x, fun y => ?_⟩
  have h := congrArg (fun g : StrongDual ℝ E => g y)
    (e.apply_symm_apply f.toContinuousLinearMap)
  rw [real_inner_comm x y]
  exact h

/-- For a nonzero descent coefficient, the affine slice meets the noncentral Levi flat
    at a unique point. -/
theorem existsUnique_descentPoint {a z a₁ L : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) (hzL : z ≤ L) (hLa₁ : L ≤ a₁)
    (hd : dDescent a z a₁ L ≠ 0) {ξ : E} (hξ : ξ ∈ a₁ ⊓ aᗮ) :
    ∃! p : E, p ∈ L ⊓ zᗮ ∧ p - ξ ∈ a ⊓ zᗮ := by
  let A : Submodule ℝ E := a ⊓ zᗮ
  let W : Submodule ℝ E := a₁ ⊓ Lᗮ
  let f := descentProjection a z a₁ L
  have hf := (dDescent_ne_zero_iff hza haa₁ hzL).mp hd
  let e : W ≃ₗ[ℝ] A := LinearEquiv.ofBijective f hf
  let l : Module.Dual ℝ W := -((innerₗ E ξ).comp W.subtype)
  obtain ⟨x, hx⟩ := exists_inner_eq_dual (l.comp e.symm.toLinearMap)
  have hpair (w : W) : ⟪(w : E), (x : E)⟫ = -⟪(w : E), ξ⟫ := by
    have h := hx (e w)
    change ⟪A.orthogonalProjectionOnto (w : E), x⟫ =
      l (e.symm (e w)) at h
    rw [inner_orthogonalProjectionOnto_eq_of_mem_right, LinearEquiv.symm_apply_apply] at h
    simpa [l, real_inner_comm] using h
  let p : E := ξ + (x : E)
  have hw (w : E) (hw : w ∈ W) : ⟪w, p⟫ = 0 := by
    change ⟪w, ξ + (x : E)⟫ = 0
    rw [inner_add_right, hpair ⟨w, hw⟩, add_neg_cancel]
  have hpL : p ∈ L := by
    rw [← orthogonal_inf_orthogonal_inf_of_le hLa₁]
    refine ⟨?_, a₁.add_mem hξ.1 (haa₁ x.prop.1)⟩
    rw [inf_comm]
    exact hw
  have hpA : p - ξ ∈ A := by simp [p]
  refine ⟨p, ⟨⟨hpL, zᗮ.add_mem (orthogonal_le hza hξ.2) x.prop.2⟩, hpA⟩, ?_⟩
  rintro q ⟨hq, hqA⟩
  let d : A := ⟨q - p, by
    have h := A.sub_mem hqA hpA
    convert h using 1
    abel⟩
  obtain ⟨w, hdw⟩ := hf.2 d
  change A.orthogonalProjectionOnto (w : E) = d at hdw
  have hz : ⟪(w : E), (d : E)⟫ = 0 := by
    change ⟪(w : E), q - p⟫ = 0
    rw [inner_sub_right, hw w w.prop]
    exact sub_eq_zero.mpr (inner_left_of_mem_orthogonal hq.1 w.prop.2)
  have hd0 : d = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rwa [← hdw, inner_orthogonalProjectionOnto_eq_of_mem_right, hdw]
  exact sub_eq_zero.mp (congrArg Subtype.val hd0)

/-- The descent section is the sign set of the unique transverse intersection point. -/
theorem descentSection_eq_posSet {R : Finset E} {a z a₁ L : Submodule ℝ E}
    (hza : z ≤ a) (haa₁ : a ≤ a₁) (hzL : z ≤ L) (hLa₁ : L ≤ a₁)
    (hd : dDescent a z a₁ L ≠ 0) {ξ p : E} (hξ : ξ ∈ a₁ ⊓ aᗮ)
    (hpL : p ∈ L ⊓ zᗮ) (hpA : p - ξ ∈ a ⊓ zᗮ) :
    descentSection R a z ξ L = posSet R p := by
  have he : ∃ q, q ∈ L ⊓ zᗮ ∧ q - ξ ∈ a ⊓ zᗮ := ⟨p, hpL, hpA⟩
  rw [descentSection, dite_eq_left he]
  obtain ⟨q, _, hu⟩ := existsUnique_descentPoint hza haa₁ hzL hLa₁ hd hξ
  rw [hu _ he.choose_spec, hu _ ⟨hpL, hpA⟩]

end Langlands.GMFamily
