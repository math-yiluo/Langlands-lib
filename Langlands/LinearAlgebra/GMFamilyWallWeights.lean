import Langlands.LinearAlgebra.GMFamilyGramVolume
import Langlands.LinearAlgebra.GMFamilySmoothDivision

/-! # Opposite wall residues for `(G, M)`-families -/

noncomputable section

open Classical
open scoped RealInnerProductSpace ContDiff

namespace Langlands.GMFamily

section GramVolume

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

private theorem gramVolume_opposite {x y : ι → E} (j : ι)
    (hj : y j = -x j) (h : ∀ i, y i - x i ∈ ℝ ∙ x j) : gramVolume y = gramVolume x := by
  choose d hd using (fun i => Submodule.mem_span_singleton.mp (h i))
  let c (i : ι) := if i = j then -1 else d i
  let A : Matrix ι ι ℝ := (1 : Matrix ι ι ℝ).updateCol j c
  have hA : A.det = -1 := by
    have heq : c = fun k => ∑ i, c i • (1 : Matrix ι ι ℝ) k i := by
      funext k
      simp [Matrix.one_apply, Finset.sum_ite_eq, smul_eq_mul]
    change ((1 : Matrix ι ι ℝ).updateCol j c).det = _
    rw [heq, Matrix.det_updateCol_sum]
    simp [c]
  have hy (i : ι) : y i = ∑ k, A i k • x k := by
    by_cases hi : i = j
    · subst i
      rw [hj, Finset.sum_eq_single j]
      · simp [A, c]
      · intro k _ hk
        simp [A, hk, Ne.symm hk]
      · simp
    · have heq : y i = x i + d i • x j := by rw [hd]; abel
      rw [heq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [A, Matrix.updateCol_self, c, ite_eq_right hi]
      rw [Finset.sum_eq_single i]
      · simp [hi, add_comm]
      · intro k hk hki
        simp [(Finset.mem_erase.mp hk).1, Ne.symm hki]
      · simp [hi]
  let G : Matrix ι ι ℝ := Matrix.of fun i k => ⟪x i, x k⟫
  have hG : (Matrix.of fun i k => ⟪y i, y k⟫) = A * G * A.transpose := by
    apply Matrix.ext
    intro i k
    change ⟪y i, y k⟫ = (A * G * A.transpose) i k
    rw [hy i, hy k, sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right,
      Matrix.mul_apply, Matrix.transpose_apply, G, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  unfold gramVolume
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hA]
  congr 1
  ring

end GramVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {a : Submodule ℝ E} {R S T U : Finset E} {v : a}

/-- Evaluation at a root, written in the imaginary parameter convention. -/
def parameterFactor (v : a) (Λ : StrongDual ℝ a) : ℂ :=
  imaginaryFactor (ContinuousLinearMap.apply ℝ ℝ v) Λ

omit [FiniteDimensional ℝ E] in
@[simp] theorem parameterFactor_eq_zero (Λ : StrongDual ℝ a) (u : a) :
    parameterFactor u Λ = 0 ↔ Λ u = 0 := imaginaryFactor_eq_zero

/-- The chamber polynomial with its volume factor and its individual linear factors displayed. -/
theorem theta_eq_product (S : Finset E) (Λ : StrongDual ℝ a) :
    theta a S Λ = ((gramVolume (fun i : simpleRoots a S => ((i : a) : E)) : ℝ) : ℂ)⁻¹ *
      ∏ u ∈ simpleRoots a S, parameterFactor u Λ := by
  rw [theta, thetaOf, ← Finset.prod_attach (s := simpleRoots a S)]
  rfl

/-- The wall adjacency relation reverses along the negative simple root. -/
theorem IsAdjacentAlong.symm (h : IsAdjacentAlong R a S T v) : IsAdjacentAlong R a T S (-v) := by
  refine ⟨h.2.1, by simpa only [neg_neg] using h.1, fun α hα hn => ?_⟩
  apply (h.2.2 α hα _).symm
  intro t ht
  exact hn (-t) (by simpa only [neg_smul, smul_neg, neg_neg] using ht)

private theorem mem_chamber_iff {S : Finset E} {h : a} {x : E} (hx : x ∈ R)
    (hS : S = posSet R h) : x ∈ S ↔ 0 < ⟪restrictedRoot a x, h⟫ := by
  rw [hS, posSet, Finset.mem_filter, and_iff_right hx, restrictedRoot,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

set_option maxHeartbeats 700000 in
/-- The adjacent chamber along a specified simple root is unique. -/
theorem adjacentAlong_unique (hT : T ∈ parabolics R a) (hU : U ∈ parabolics R a)
    (hA : IsAdjacentAlong R a S T v) (hB : IsAdjacentAlong R a S U v) : T = U := by
  obtain ⟨hTR, ⟨x, hx, hTx⟩⟩ := Finset.mem_filter.mp hT
  obtain ⟨hUR, ⟨y, hy, hUy⟩⟩ := Finset.mem_filter.mp hU
  let x' : a := ⟨x, hx.1⟩
  let y' : a := ⟨y, hy.1⟩
  have hnx : ⟪v, x'⟫ < 0 := by
    have hp := simpleRoot_pos (h := x') (hTx ▸ hA.2.1)
    simpa only [inner_neg_left, neg_pos] using hp
  have hny : ⟪v, y'⟫ < 0 := by
    have hp := simpleRoot_pos (h := y') (hUy ▸ hB.2.1)
    simpa only [inner_neg_left, neg_pos] using hp
  ext α
  by_cases hα : α ∈ R
  · by_cases hn : ∀ t : ℝ, restrictedRoot a α ≠ t • v
    · exact (hA.2.2 α hα hn).symm.trans (hB.2.2 α hα hn)
    · push Not at hn
      obtain ⟨t, ht⟩ := hn
      rw [mem_chamber_iff (h := x') hα hTx, mem_chamber_iff (h := y') hα hUy,
        ht, real_inner_smul_left, real_inner_smul_left]
      simp only [mul_pos_iff, hnx, hny, hnx.not_gt, hny.not_gt, and_true, and_false, false_or]
  · exact iff_of_false (fun h => hα (Finset.mem_powerset.mp hTR h))
      (fun h => hα (Finset.mem_powerset.mp hUR h))

/-- Adjacency across a wall changes the chamber. -/
theorem adjacentAlong_ne (hS : S ∈ parabolics R a) (hA : IsAdjacentAlong R a S T v) : S ≠ T := by
  rintro rfl
  obtain ⟨_, ⟨x, hx, rfl⟩⟩ := Finset.mem_filter.mp hS
  let h : a := ⟨x, hx.1⟩
  have hp := simpleRoot_pos (h := h) hA.1
  have hn := simpleRoot_pos (h := h) hA.2.1
  rw [inner_neg_left] at hn
  linarith

/-- The two chamber bases along a wall have the same Euclidean covolume. Their products with the
wall factors removed agree on the dual hyperplane. -/
theorem volume_and_product_erase_of_adjacentAlong (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hT : T ∈ parabolics R a) (hA : IsAdjacentAlong R a S T v) :
    gramVolume (fun i : simpleRoots a S => ((i : a) : E)) =
      gramVolume (fun i : simpleRoots a T => ((i : a) : E)) ∧
    ∀ Λ : StrongDual ℝ a, Λ v = 0 →
      (∏ u ∈ (simpleRoots a S).erase v, parameterFactor u Λ) =
      ∏ u ∈ (simpleRoots a T).erase (-v), parameterFactor u Λ := by
  obtain ⟨e, hev, he⟩ := exists_simpleRoots_equiv_of_adjacentAlong hR ha hS hT hA
  let x (i : simpleRoots a S) : E := ((i : a) : E)
  let y (i : simpleRoots a T) : E := ((i : a) : E)
  refine ⟨?_, fun Λ hΛ => ?_⟩
  · change gramVolume x = gramVolume y
    rw [← gramVolume_reindex e y]
    symm
    apply gramVolume_opposite (⟨v, hA.1⟩ : simpleRoots a S)
    · exact congrArg (fun u : a => (u : E)) hev
    · intro i
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (he i)
      exact Submodule.mem_span_singleton.mpr ⟨r, congrArg (fun u : a => (u : E)) hr⟩
  · have heval (i : simpleRoots a S) : Λ (e i) = Λ i := by
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (he i)
      have h := congrArg Λ hr
      rw [map_smul, hΛ, smul_zero, map_sub] at h
      exact sub_eq_zero.mp h.symm
    refine Finset.prod_bij (fun u hu => (e ⟨u, Finset.mem_of_mem_erase hu⟩ : a))
      (fun u hu => ?_) (fun u hu w hw heq => ?_) (fun w hw => ?_) (fun u hu => ?_)
    · apply Finset.mem_erase.mpr
      refine ⟨fun h => (Finset.mem_erase.mp hu).1 ?_, (e _).property⟩
      exact congrArg Subtype.val (e.injective (Subtype.ext (h.trans hev.symm)))
    · exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    · let j : simpleRoots a T := ⟨w, Finset.mem_of_mem_erase hw⟩
      let i := e.symm j
      have hi : (i : a) ≠ v := fun hi => (Finset.mem_erase.mp hw).1 (by
        have h := congrArg (fun k => (e k : a)) (Subtype.ext hi : i = ⟨v, hA.1⟩)
        simpa only [i, e.apply_symm_apply, hev] using h)
      exact ⟨i, Finset.mem_erase.mpr ⟨hi, i.property⟩, congrArg Subtype.val (e.apply_symm_apply j)⟩
    · exact congrArg (fun t : ℝ => Complex.I * (t : ℂ)) (heval ⟨u, Finset.mem_of_mem_erase hu⟩).symm

end Langlands.GMFamily
