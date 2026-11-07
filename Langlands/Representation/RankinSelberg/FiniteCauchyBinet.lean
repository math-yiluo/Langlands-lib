import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort

/-! # Ordered finite Cauchy–Binet expansion -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open Function

/-- Enumerate an ordered subset after permuting its positions. -/
def subsetPermutationEmbedding {κ : Type*} [LinearOrder κ] {m : ℕ}
    (p : Σ _S : {S : Finset κ // S.card = m}, Equiv.Perm (Fin m)) : Fin m ↪ κ :=
  p.2.toEmbedding.trans (p.1.val.orderEmbOfFin p.1.property).toEmbedding

theorem map_subsetPermutationEmbedding_univ {κ : Type*} [LinearOrder κ] {m : ℕ}
    (p : Σ _S : {S : Finset κ // S.card = m}, Equiv.Perm (Fin m)) :
    Finset.univ.map (subsetPermutationEmbedding p) = p.1.val := by
  rw [subsetPermutationEmbedding, ← Finset.map_map, Finset.map_univ_equiv,
    Finset.map_orderEmbOfFin_univ]

/-- An injection is uniquely an ordered subset together with a permutation. -/
theorem subsetPermutationEmbedding_bijective {κ : Type*} [LinearOrder κ] {m : ℕ} :
    Bijective (subsetPermutationEmbedding (κ := κ) (m := m)) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    have he := congrArg (fun e : Fin m ↪ κ => Finset.univ.map e) h
    rw [map_subsetPermutationEmbedding_univ, map_subsetPermutationEmbedding_univ] at he
    have hST : S = T := Subtype.ext he
    cases hST
    have hστ : σ = τ := by
      apply Equiv.ext
      intro i
      apply (S.val.orderEmbOfFin S.property).injective
      exact congrArg (fun e : Fin m ↪ κ => e i) h
    cases hστ
    rfl
  · intro p
    let S : {S : Finset κ // S.card = m} :=
      ⟨Finset.univ.map p, by simp⟩
    let f : Fin m → Fin m := fun i =>
      (S.val.orderIsoOfFin S.property).symm ⟨p i, by simp [S]⟩
    have hfac (i : Fin m) : S.val.orderEmbOfFin S.property (f i) = p i := by
      change ((S.val.orderIsoOfFin S.property)
        ((S.val.orderIsoOfFin S.property).symm ⟨p i, _⟩) : κ) = p i
      simp
    have hinj : Injective f := by
      intro i j hij
      apply p.injective
      rw [← hfac i, ← hfac j, hij]
    let σ : Equiv.Perm (Fin m) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    refine ⟨⟨S, σ⟩, ?_⟩
    apply Function.Embedding.ext
    intro i
    exact hfac i

/-- The image-subset/permutation equivalence for finite ordered minors. -/
def subsetPermutationEquiv {κ : Type*} [LinearOrder κ] (m : ℕ) :
    (Σ _S : {S : Finset κ // S.card = m}, Equiv.Perm (Fin m)) ≃ (Fin m ↪ κ) :=
  Equiv.ofBijective subsetPermutationEmbedding subsetPermutationEmbedding_bijective

section Determinant

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] {m : ℕ}

omit [DecidableEq κ] in
/-- Row multilinearity expands a rectangular product over all index choices. -/
theorem det_rectangular_mul_eq_sum_functions
    (A : Matrix (Fin m) κ R) (B : Matrix κ (Fin m) R) :
    Matrix.det (A * B) = ∑ f : Fin m → κ,
      (∏ i, A i (f i)) * Matrix.det (B.submatrix f id) := by
  have hrows : A * B = fun i => ∑ k : κ, A i k • B k := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrows]
  change Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ k : κ, A i k • B k) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [MultilinearMap.map_smul_univ]
  rfl

/-- Repeated index choices vanish, so only injections contribute. -/
theorem det_rectangular_mul_eq_sum_embeddings
    (A : Matrix (Fin m) κ R) (B : Matrix κ (Fin m) R) :
    Matrix.det (A * B) = ∑ f : Fin m ↪ κ,
      (∏ i, A i (f i)) * Matrix.det (B.submatrix f id) := by
  rw [det_rectangular_mul_eq_sum_functions]
  have hz (f : Fin m → κ) (hf : ¬ Injective f) : Matrix.det (B.submatrix f id) = 0 := by
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨i, j, he, hij⟩ := hf
    apply Matrix.det_zero_of_row_eq hij
    funext k
    exact congrArg (fun a => B a k) he
  calc
    _ = ∑ f : Fin m → κ with Injective f,
        (∏ i, A i (f i)) * Matrix.det (B.submatrix f id) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      rw [hz f (by simpa using hf), mul_zero]
    _ = _ := by
      apply Finset.sum_bij (fun f hf => (⟨f, (Finset.mem_filter.mp hf).2⟩ : Fin m ↪ κ))
      · intro f hf
        exact Finset.mem_univ _
      · intro f hf g hg h
        exact congrArg (fun e : Fin m ↪ κ => e.toFun) h
      · intro f _
        exact ⟨f, by simp [f.injective], rfl⟩
      · intro f hf
        rfl

/-- Cauchy–Binet indexed by increasingly ordered image subsets. -/
theorem det_rectangular_mul [LinearOrder κ]
    (A : Matrix (Fin m) κ R) (B : Matrix κ (Fin m) R) :
    Matrix.det (A * B) =
      ∑ S : {S : Finset κ // S.card = m},
        Matrix.det (A.submatrix id (S.val.orderEmbOfFin S.property)) *
          Matrix.det (B.submatrix (S.val.orderEmbOfFin S.property) id) := by
  rw [det_rectangular_mul_eq_sum_embeddings,
    ← Equiv.sum_comp (subsetPermutationEquiv (κ := κ) m), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  let e := S.val.orderEmbOfFin S.property
  have hdet (σ : Equiv.Perm (Fin m)) :
      Matrix.det (B.submatrix (subsetPermutationEquiv m ⟨S, σ⟩) id) =
        (Equiv.Perm.sign σ : ℤ) * Matrix.det (B.submatrix e id) := by
    exact Matrix.det_permute σ (B.submatrix e id)
  simp_rw [hdet]
  rw [← Matrix.det_transpose (A.submatrix id e), Matrix.det_apply' ((A.submatrix id e).transpose), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  change (∏ i, A i (e (σ i))) *
      ((Equiv.Perm.sign σ : ℤ) * Matrix.det (B.submatrix e id)) =
    ((Equiv.Perm.sign σ : ℤ) * ∏ i, A i (e (σ i))) * Matrix.det (B.submatrix e id)
  ring

end Determinant

end Langlands.GeneralLinear.Spherical
