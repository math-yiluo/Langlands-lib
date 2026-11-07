import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Reductive.GeneralLinearWeyl
import Mathlib.Data.Matrix.PEquiv

/-! # Permutation conjugation of block unipotent subgroups of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

section Matrix

variable (A : Type*) [CommRing A]

omit [Fintype n] in
/-- The permutation matrix of `w`, whose `(a, b)` entry is one exactly when `a = w b`, is the
partial-equivalence matrix of `w⁻¹`. -/
theorem permMatrix_eq_toMatrix (w : Equiv.Perm n) :
    permMatrix A w = w.symm.toPEquiv.toMatrix := by
  ext a b
  rw [permMatrix, Matrix.of_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  exact if_congr (by rw [Option.mem_def, Option.some_inj, Equiv.symm_apply_eq]) rfl rfl

/-- Conjugation by the permutation matrix of `τ⁻¹` permutes rows and columns by `τ`. -/
theorem permGL_symm_conj_apply (τ : n ≃ n) (g : GL n A) (i j : n) :
    ((permGL A τ.symm * g * (permGL A τ.symm)⁻¹ : GL n A) : Matrix n n A) i j =
      (g : Matrix n n A) (τ i) (τ j) := by
  change (permMatrix A τ.symm * (g : Matrix n n A) * permMatrix A τ.symm⁻¹) i j = _
  rw [permMatrix_eq_toMatrix, permMatrix_eq_toMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

variable {A} in
/-- Conjugation by the permutation matrix of `τ⁻¹` carries the block unipotent subgroup of a
weight `w` onto that of the permuted weight `v = w ∘ τ`. -/
theorem permGL_symm_conj_mem_blockUnipotentSubgroup_iff {τ : n ≃ n} {v w : n → ℤ}
    (hv : ∀ k, w (τ k) = v k) (g : GL n A) :
    permGL A τ.symm * g * (permGL A τ.symm)⁻¹ ∈ blockUnipotentSubgroup A v ↔
      g ∈ blockUnipotentSubgroup A w := by
  simp only [mem_blockUnipotentSubgroup, permGL_symm_conj_apply]
  constructor
  · intro hg k l hkl
    obtain ⟨i, rfl⟩ := τ.surjective k
    obtain ⟨j, rfl⟩ := τ.surjective l
    rw [hv, hv] at hkl
    rw [hg i j hkl]
    simp only [Matrix.one_apply, τ.injective.eq_iff]
  · intro hg i j hij
    rw [← hv, ← hv] at hij
    rw [hg _ _ hij]
    simp only [Matrix.one_apply, τ.injective.eq_iff]

end Matrix

section Scheme

variable {R : CommRingCat.{u}}

/-- Conjugation by the permutation point of `τ⁻¹` carries the block unipotent subgroup functor of
`w` onto that of `v = w ∘ τ`: the former is the inverse image of the latter under the inner
automorphism. -/
theorem blockUnipotent_eq_comap_innerIso_permPoint {τ : n ≃ n} {v w : n → ℤ}
    (hv : ∀ k, w (τ k) = v k) :
    blockUnipotent n R w =
      (blockUnipotent n R v).comap ((groupScheme n R).innerIso (permPoint R τ.symm)).hom := by
  ext T x
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]
  change pointsEquiv n R T x ∈ blockUnipotentSubgroup _ w ↔
    pointsEquiv n R T _ ∈ blockUnipotentSubgroup _ v
  rw [map_mul, map_mul, map_inv, pointsEquiv_constantPoint_permPoint,
    permGL_symm_conj_mem_blockUnipotentSubgroup_iff hv]

end Scheme

section Threshold

/-- The two-level weight that is one on the indices `k` with `c < e k` and zero elsewhere. -/
def thresholdWeight (e : n → ℤ) (c : ℤ) (k : n) : ℤ :=
  if c < e k then 1 else 0

omit [Fintype n] [DecidableEq n] in
/-- The threshold weight is a weakly increasing function of `e`. -/
theorem thresholdWeight_le_of_le (e : n → ℤ) (c : ℤ) {i j : n} (hij : e i ≤ e j) :
    thresholdWeight e c i ≤ thresholdWeight e c j := by
  unfold thresholdWeight
  split_ifs with hi hj hj
  · exact le_rfl
  · exact absurd (hi.trans_le hij) hj
  · exact zero_le_one
  · exact le_rfl

/-- After renumbering by a permutation, a threshold weight on `Fin n` is the original two-block
weight with `a` upper indices first and `b` lower indices last. The upper block is nonempty
exactly when some `e k` exceeds `c`, and the lower block exactly when some `e k` is at most
`c`. -/
theorem exists_perm_thresholdWeight_eq_twoBlockWeight {m : ℕ} (e : Fin m → ℤ) (c : ℤ) :
    ∃ (a b : ℕ) (h : a + b = m) (τ : Fin m ≃ Fin m),
      (0 < a ↔ ∃ k, c < e k) ∧ (0 < b ↔ ∃ k, e k ≤ c) ∧
        ∀ k, thresholdWeight e c (τ k) = Langlands.GeneralLinear.twoBlockWeight h k := by
  classical
  let p : Fin m → Prop := fun k => c < e k
  let a := Fintype.card {k // p k}
  let b := Fintype.card {k // ¬p k}
  have h : a + b = m := by
    have hle := Fintype.card_subtype_le p
    change Fintype.card {k // p k} + Fintype.card {k // ¬p k} = m
    rw [Fintype.card_subtype_compl, Fintype.card_fin] at *
    omega
  let σ : Fin a ⊕ Fin b ≃ Fin m :=
    (Equiv.sumCongr (Fintype.equivFin {k // p k}).symm
      (Fintype.equivFin {k // ¬p k}).symm).trans (Equiv.sumCompl p)
  refine ⟨a, b, h, (finSumFinEquiv.trans (finCongr h)).symm.trans σ, ?_, ?_, ?_⟩
  · rw [Fintype.card_pos_iff]
    exact ⟨fun ⟨k⟩ => ⟨k.val, k.property⟩, fun ⟨k, hk⟩ => ⟨⟨k, hk⟩⟩⟩
  · rw [Fintype.card_pos_iff]
    exact ⟨fun ⟨k⟩ => ⟨k.val, not_lt.mp k.property⟩, fun ⟨k, hk⟩ => ⟨⟨k, not_lt.mpr hk⟩⟩⟩
  · intro k
    obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective k
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    cases s with
    | inl i =>
      rw [Langlands.GeneralLinear.twoBlockWeight_inl]
      exact ite_eq_left ((Fintype.equivFin {k // p k}).symm i).property
    | inr j =>
      rw [Langlands.GeneralLinear.twoBlockWeight_inr]
      exact ite_eq_right ((Fintype.equivFin {k // ¬p k}).symm j).property

end Threshold

end Langlands.GroupScheme.GeneralLinear
