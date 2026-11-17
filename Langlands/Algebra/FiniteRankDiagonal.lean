import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finitely supported diagonals of finite-rank matrices -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.FiniteRankDiagonal

variable {A : Type u} [CommRing A] {M : Type v}

/-- The outer-product bilinear map, with no finiteness condition on the index set. -/
def outerProduct : (M → A) →ₗ[A] (M → A) →ₗ[A] (M × M → A) where
  toFun b :=
    { toFun := fun c p => b p.1 * c p.2
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }
  map_add' := by intros; ext; simp [add_mul]
  map_smul' := by intros; ext; simp [mul_assoc]

/-- Matrix coefficients of a tensor of arbitrary coefficient families. -/
def coefficients : (M → A) ⊗[A] (M → A) →ₗ[A] (M × M → A) :=
  TensorProduct.lift outerProduct

@[simp] theorem coefficients_tmul (b c : M → A) (m n : M) :
    coefficients (b ⊗ₜ[A] c) (m, n) = b m * c n := rfl

/-- The columns of a finite-rank matrix lie in one finitely generated module. -/
theorem exists_finite_column_span (t : (M → A) ⊗[A] (M → A)) :
    ∃ B : Finset (M → A), ∀ n : M,
      (fun m => coefficients t (m, n)) ∈ Submodule.span A (B : Set (M → A)) := by
  classical
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
      refine ⟨{b}, fun n => ?_⟩
      have h : (fun m => coefficients (b ⊗ₜ[A] c) (m, n)) = c n • b := by
        ext m
        simp [mul_comm]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add t s ht hs =>
      obtain ⟨B, hB⟩ := ht
      obtain ⟨C, hC⟩ := hs
      refine ⟨B ∪ C, fun n => ?_⟩
      rw [map_add]
      change (fun m => coefficients t (m, n) + coefficients s (m, n)) ∈ _
      exact Submodule.add_mem _
        (Submodule.span_mono (by simp) (hB n))
        (Submodule.span_mono (by simp) (hC n))

/-- A finitely generated submodule of a direct sum has a common finite support. -/
theorem exists_support_bound {P : Submodule A (M →₀ A)} (hP : P.FG) :
    ∃ K : Finset M, P ≤ Finsupp.supported A A (K : Set M) := by
  classical
  obtain ⟨B, hB⟩ := hP
  refine ⟨B.biUnion Finsupp.support, ?_⟩
  rw [← hB]
  refine Submodule.span_le.mpr ?_
  intro b hb
  exact fun m hm => Finset.mem_biUnion.mpr ⟨b, hb, hm⟩

/-- If every one-coordinate vector lies in a fixed finite span in the product module,
only finitely many of these vectors can be nonzero over a noetherian ring. -/
theorem finite_support_of_single_mem_finite_span [IsNoetherianRing A]
    (a : M → A) (B : Finset (M → A))
    (ha : ∀ m : M,
      Finsupp.lcoeFun (R := A) (Finsupp.single m (a m)) ∈
        Submodule.span A (B : Set (M → A))) :
    (Function.support a).Finite := by
  classical
  let V := Submodule.span A (B : Set (M → A))
  let P := V.comap (Finsupp.lcoeFun (R := A))
  have hP : P.FG := Submodule.fg_of_fg_map_injective
    (Finsupp.lcoeFun (R := A)) (fun _ _ h => Finsupp.ext (congrFun h))
    ((Submodule.fg_span B.finite_toSet).of_le
      (Submodule.map_comap_le (Finsupp.lcoeFun (R := A)) V))
  obtain ⟨K, hK⟩ := exists_support_bound hP
  refine K.finite_toSet.subset ?_
  intro m hm
  change a m ≠ 0 at hm
  have hs := hK (ha m)
  exact hs (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff,
    Finsupp.single_eq_same] using hm)

/-- SGA 3, IX, Lemma 7.2: a diagonal matrix in the image of the tensor-to-product map has
finite diagonal support over a noetherian ring. -/
theorem finite_support_diagonal [IsNoetherianRing A]
    (t : (M → A) ⊗[A] (M → A))
    (hd : ∀ m n : M, m ≠ n → coefficients t (m, n) = 0) :
    (Function.support (fun m => coefficients t (m, m))).Finite := by
  classical
  obtain ⟨B, hB⟩ := exists_finite_column_span t
  apply finite_support_of_single_mem_finite_span _ B
  intro n
  have h : Finsupp.lcoeFun (R := A) (Finsupp.single n (coefficients t (n, n))) =
      fun m => coefficients t (m, n) := by
    ext m
    by_cases hmn : m = n
    · subst m
      simp
    · simp [Ne.symm hmn, hd m n hmn]
  rw [h]
  exact hB n

/-- The actual finite coefficient family of a finite-rank diagonal matrix. -/
def diagonalFinsupp [IsNoetherianRing A]
    (t : (M → A) ⊗[A] (M → A))
    (hd : ∀ m n : M, m ≠ n → coefficients t (m, n) = 0) : M →₀ A :=
  Finsupp.ofSupportFinite _ (finite_support_diagonal t hd)

@[simp] theorem diagonalFinsupp_apply [IsNoetherianRing A]
    (t : (M → A) ⊗[A] (M → A))
    (hd : ∀ m n : M, m ≠ n → coefficients t (m, n) = 0) (m : M) :
    diagonalFinsupp t hd m = coefficients t (m, m) := rfl

end Langlands.FiniteRankDiagonal
