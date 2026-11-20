import Langlands.LinearAlgebra.MatrixConjugationSlice
import Langlands.LinearAlgebra.RealSpectralSimilarity

/-! # Smooth coordinates containing the fixed spectral label locus -/

noncomputable section

open Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "tangentOf" A => LinearMap.range (matrixConjugationTangent A)

/-- Transverse directions from the polynomial semisimple part of a real matrix. -/
def realMatrixSemisimpleDirections (A : Mat) : Submodule ℝ Mat :=
  (Algebra.adjoin ℝ {matrixSemisimplePart A}).toSubmodule

theorem realMatrixSemisimpleDirections_le_adjoin (A : Mat) :
    realMatrixSemisimpleDirections A ≤ (Algebra.adjoin ℝ {A}).toSubmodule :=
  Algebra.adjoin_singleton_le (matrixSemisimplePart_mem_adjoin A)

theorem commute_realMatrixSemisimpleDirections {A X Z : Mat} (hX : Commute X A)
    (hZ : Z ∈ realMatrixSemisimpleDirections A) : Commute X Z :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute (realMatrixSemisimpleDirections_le_adjoin A hZ) hX

theorem disjoint_tangent_realMatrixSemisimpleDirections (A : Mat) :
    Disjoint (tangentOf A) (realMatrixSemisimpleDirections A) := by
  let Z := realMatrixSemisimpleDirections A
  have hnd : (matrixTraceBilin.restrict Z).Nondegenerate :=
    matrixTraceBilin_restrict_adjoin_nondegenerate (matrixSemisimplePart_isSemisimple A)
  apply Submodule.disjoint_def.mpr
  intro X hX hXZ
  have hz : (⟨X, hXZ⟩ : Z) = 0 := hnd.1 _ (fun Y => by
    change matrixTraceBilin X (Y : Mat) = 0
    have horth := (mem_matrixTraceBilin_orthogonal_conjugationTangent_iff A (Y : Mat)).mpr
      (commute_realMatrixSemisimpleDirections (Commute.refl A) Y.property)
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp horth) X hX)
  exact congrArg Subtype.val hz

theorem ker_matrixConjugationTangent_le_add_semisimpleDirection {A Z : Mat}
    (hZ : Z ∈ realMatrixSemisimpleDirections A) :
    LinearMap.ker (matrixConjugationTangent A) ≤ LinearMap.ker (matrixConjugationTangent (A + Z)) := by
  intro X hX
  have hXC : Commute X A := sub_eq_zero.mp (LinearMap.mem_ker.mp hX)
  apply LinearMap.mem_ker.mpr
  rw [matrixConjugationTangent_apply, (hXC.add_right (commute_realMatrixSemisimpleDirections hXC hZ)).eq,
    sub_self]

theorem finrank_range_matrixConjugationTangent_add_semisimpleDirection_le {A Z : Mat}
    (hZ : Z ∈ realMatrixSemisimpleDirections A) :
    Module.finrank ℝ (tangentOf (A + Z)) ≤ Module.finrank ℝ (tangentOf A) := by
  have h := Submodule.finrank_mono (ker_matrixConjugationTangent_le_add_semisimpleDirection hZ)
  have hA := (matrixConjugationTangent A).finrank_range_add_finrank_ker
  have hAZ := (matrixConjugationTangent (A + Z)).finrank_range_add_finrank_ker
  omega

/-- Small polynomial semisimple shifts preserve the centralizer. -/
theorem eventually_ker_matrixConjugationTangent_add_semisimpleDirection_eq (A : Mat) :
    ∀ᶠ Z in 𝓝 (0 : Mat), Z ∈ realMatrixSemisimpleDirections A →
      LinearMap.ker (matrixConjugationTangent (A + Z)) = LinearMap.ker (matrixConjugationTangent A) := by
  let L (B : Mat) : Mat →L[ℝ] Mat := (matrixConjugationTangent B).toContinuousLinearMap
  let r (B : Mat) := Module.finrank ℝ (tangentOf B)
  have hL : Continuous L := continuous_clm_apply.mpr (fun x =>
    (continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const))
  have hrank (B : Mat) : (r B : Cardinal) = (L B).toLinearMap.rank :=
    Module.finrank_eq_rank ℝ _
  have hopen : IsOpen {B | r A ≤ r B} := by
    convert (isOpen_setOfPred_nat_le_rank (r A)).preimage hL using 1
    ext B
    change r A ≤ r B ↔ (r A : Cardinal) ≤ (L B).toLinearMap.rank
    rw [← hrank]
    exact_mod_cast (Iff.rfl : r A ≤ r B ↔ r A ≤ r B)
  have hnear : ∀ᶠ B in 𝓝 A, r A ≤ r B :=
    hopen.mem_nhds (Set.mem_ofPred.mpr le_rfl)
  have hcont : Continuous (fun Z : Mat => A + Z) := continuous_const.add continuous_id
  have hshift : Tendsto (fun Z : Mat => A + Z) (𝓝 0) (𝓝 A) := by
    simpa only [add_zero] using hcont.tendsto (0 : Mat)
  filter_upwards [hshift.eventually hnear] with Z hZrank hZ
  symm
  apply Submodule.eq_of_le_of_finrank_le (ker_matrixConjugationTangent_le_add_semisimpleDirection hZ)
  have hA := (matrixConjugationTangent A).finrank_range_add_finrank_ker
  have hAZ := (matrixConjugationTangent (A + Z)).finrank_range_add_finrank_ker
  change Module.finrank ℝ (tangentOf A) ≤ Module.finrank ℝ (tangentOf (A + Z)) at hZrank
  omega

theorem orthogonal_matrixConjugationTangent_eq_ker (A : Mat) :
    matrixTraceBilin.orthogonal (tangentOf A) = LinearMap.ker (matrixConjugationTangent A) := by
  ext X
  rw [mem_matrixTraceBilin_orthogonal_conjugationTangent_iff, LinearMap.mem_ker,
    matrixConjugationTangent_apply, sub_eq_zero]
  exact ⟨fun h => h.eq.symm, fun h => h.symm⟩

/-- The tangent image also remains constant on the small semisimple slice. -/
theorem eventually_range_matrixConjugationTangent_add_semisimpleDirection_eq (A : Mat) :
    ∀ᶠ Z in 𝓝 (0 : Mat), Z ∈ realMatrixSemisimpleDirections A →
      (tangentOf (A + Z)) = (tangentOf A) := by
  let B : LinearMap.BilinForm ℝ Mat := matrixTraceBilin
  have hB : B.IsRefl := fun X Y h => (matrixTraceBilin_isSymm.eq Y X).trans h
  have hdouble := LinearMap.BilinForm.orthogonal_orthogonal matrixTraceBilin_nondegenerate hB
  filter_upwards [eventually_ker_matrixConjugationTangent_add_semisimpleDirection_eq A] with Z hZ hmem
  have h := hZ hmem
  rw [← orthogonal_matrixConjugationTangent_eq_ker, ← orthogonal_matrixConjugationTangent_eq_ker] at h
  exact (hdouble (tangentOf (A + Z))).symm.trans
    ((congrArg B.orthogonal h).trans (hdouble (tangentOf A)))

theorem conjugate_add_semisimpleDirection_eq {A Z : Mat} {u : Matˣ}
    (h : Commute (u : Mat) A) (hz : Z ∈ realMatrixSemisimpleDirections A) :
    u.val * (A + Z) * u.inv = A + Z := by
  rw [(h.add_right (commute_realMatrixSemisimpleDirections h hz)).eq, mul_assoc, u.val_inv, mul_one]

theorem adjustedTranspose_add_semisimpleDirection_eq {A Z : Mat} {q : Matˣ}
    (h : q.val * A * q.inv = Aᵀ) (hz : Z ∈ realMatrixSemisimpleDirections A) :
    q.inv * (A + Z)ᵀ * q.val = A + Z := by
  have hm : A + Z ∈ Algebra.adjoin ℝ {A} :=
    (Algebra.adjoin ℝ {A}).add_mem (Algebra.subset_adjoin (Set.mem_singleton A))
      (realMatrixSemisimpleDirections_le_adjoin A hz)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, hp⟩ := hm
  change Polynomial.aeval A p = A + Z at hp
  have hq : SemiconjBy q.inv Aᵀ A := by
    change q.inv * Aᵀ = A * q.inv
    rw [← h, ← mul_assoc q.inv (q.val * A) q.inv, ← mul_assoc q.inv q.val A, q.inv_val, one_mul]
  have hqp : SemiconjBy q.inv (Polynomial.aeval Aᵀ p) (Polynomial.aeval A p) := by
    clear hp
    induction p using Polynomial.induction_on' with
    | add p p' ih ih' => simpa only [map_add] using ih.add_right ih'
    | monomial k c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      exact SemiconjBy.mul_right (Algebra.commutes c q.inv).symm (hq.pow_right k)
  rw [← hp, transpose_aeval_matrix, hqp.eq, mul_assoc, q.inv_val, mul_one]

/-- Local real matrix conjugation coordinates whose zero normal coordinate contains the nearby
fixed-label locus. A pair of nearby similar matrices with first matrix in the semisimple slice
recovers the exact semisimple coordinate under the inverse chart. -/
theorem exists_realSpectralStratumChart (A : Mat) :
    ∃ (W : Submodule ℝ Mat) (N : Submodule ℝ W) (J : (tangentOf A) →L[ℝ] Mat)
      (e : OpenPartialHomeomorph (((tangentOf A) × realMatrixSemisimpleDirections A) × N) Mat)
      (V : Set (Mat × Mat)),
      realMatrixSemisimpleDirections A ≤ W ∧ IsCompl (tangentOf A) W ∧
      IsCompl ((realMatrixSemisimpleDirections A).comap W.subtype) N ∧
      (∀ t : tangentOf A, matrixConjugationTangent A (J t) = t) ∧
      (∀ p, e p = (1 + J p.1.1) * (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) *
        Ring.inverse (1 + J p.1.1)) ∧
      0 ∈ e.source ∧ e 0 = A ∧ (∀ p ∈ e.source, IsUnit (1 + J p.1.1)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen V ∧ (A, A) ∈ V ∧
      (∀ (z : realMatrixSemisimpleDirections A) (B : Mat), (A + (z : Mat), B) ∈ V →
        (∃ u : Matˣ, (u : Mat) * (A + (z : Mat)) = B * (u : Mat)) →
        B ∈ e.target ∧ (e.symm B).1.2 = z ∧ (e.symm B).2 = 0) ∧
      ∀ᶠ B in 𝓝 A, realMatrixSpectralRankLabel B = realMatrixSpectralRankLabel A →
        B ∈ e.target ∧ (e.symm B).2 = 0 := by
  let T := tangentOf A
  let Z := realMatrixSemisimpleDirections A
  obtain ⟨W, hZW, hW⟩ := (disjoint_tangent_realMatrixSemisimpleDirections A).symm.exists_isCompl
  obtain ⟨J, a, V, hJ, ha, ha₀, haA, haunit, haf, hai, hV, hV₀, hVrank⟩ :=
    exists_matrixConjugationSlice A W hW.symm
  let ZW := Z.comap W.subtype
  obtain ⟨N, hN⟩ := ZW.exists_isCompl
  let i : Z ≃ₗ[ℝ] ZW := (Submodule.comapSubtypeEquivOfLe hZW).symm
  let E' : (Z × N) ≃ₗ[ℝ] W :=
    (i.prodCongr (LinearEquiv.refl ℝ N)).trans (ZW.prodEquivOfIsCompl N hN)
  let E : (Z × N) ≃L[ℝ] W :=
    LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := ↥Z × ↥N) (F := ↥W) E'
  let P : ((T × Z) × N) ≃L[ℝ] (T × W) :=
    (ContinuousLinearEquiv.prodAssoc ℝ T Z N).trans ((ContinuousLinearEquiv.refl ℝ T).prodCongr E)
  let e := P.toHomeomorph.transOpenPartialHomeomorph a
  have hE (z : Z) (y : N) : (E (z, y) : Mat) = (z : Mat) + ((y : W) : Mat) := rfl
  have he (p : (T × Z) × N) : e p = (1 + J p.1.1) *
      (A + (p.1.2 : Mat) + ((p.2 : W) : Mat)) * Ring.inverse (1 + J p.1.1) := by
    change a (P p) = _
    rw [ha, matrixSliceConjugation]
    change (1 + J p.1.1) * (A + (E (p.1.2, p.2) : Mat)) * Ring.inverse (1 + J p.1.1) = _
    rw [hE, add_assoc]
  have he₀ : 0 ∈ e.source := by
    change P 0 ∈ a.source
    rwa [map_zero]
  have heA : e 0 = A := by
    change a (P 0) = A
    rwa [map_zero]
  have heunit (p : (T × Z) × N) (hp : p ∈ e.source) : IsUnit (1 + J p.1.1) :=
    haunit (P p) hp
  have hef : ContDiffOn ℝ ∞ e e.source := by
    exact haf.comp_continuousLinearMap (G := (↥T × ↥Z) × ↥N) P.toContinuousLinearMap
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    exact hai.continuousLinearMap_comp (G := (↥T × ↥Z) × ↥N) P.symm.toContinuousLinearMap
  have hchart (z : Z) (B : Mat) (hm : (A + (z : Mat), B) ∈ V)
      (hsim : ∃ u : Matˣ, (u : Mat) * (A + (z : Mat)) = B * (u : Mat)) :
      B ∈ e.target ∧ (e.symm B).1.2 = z ∧ (e.symm B).2 = 0 := by
    let w : W := ⟨(z : Mat), hZW z.property⟩
    obtain ⟨u, hu⟩ := hsim
    have hRank := (finrank_range_matrixIntertwinerMap_of_conjugate _ _ u hu).trans_le
      (finrank_range_matrixConjugationTangent_add_semisimpleDirection_le z.property)
    obtain ⟨hB, hw⟩ := hVrank w B hm hRank
    have hEz : E (z, 0) = w := Subtype.ext (by rw [hE]; simp [w])
    have hp : E ((e.symm B).1.2, (e.symm B).2) = w := by
      have h := congrArg Prod.snd (P.apply_symm_apply (a.symm B))
      exact h.trans hw
    have hpair := E.injective (hp.trans hEz.symm)
    exact ⟨hB, congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  refine ⟨W, N, J, e, V, hZW, hW.symm, hN, hJ, he, he₀, heA, heunit, hef, hei, hV, hV₀, hchart, ?_⟩
  obtain ⟨U₁, hU₁, U₂, hU₂, hUV⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds hV₀)
  let D := (fun X : Mat => A + X) ⁻¹' U₁
  have hD : D ∈ 𝓝 (0 : Mat) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU₁)
  filter_upwards [eventually_exists_realSpectralShift_similar A hD, hU₂] with B hsim hB hlabel
  obtain ⟨X, hX, hXZ, hXsim⟩ := hsim hlabel
  obtain ⟨hB', _, hnormal⟩ := hchart ⟨X, hXZ⟩ B (hUV ⟨hX, hB⟩) hXsim
  exact ⟨hB', hnormal⟩

end Langlands
