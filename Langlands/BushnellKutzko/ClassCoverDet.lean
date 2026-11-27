import Langlands.BushnellKutzko.ClassCoverFibreChar
import Langlands.BushnellKutzko.FiltrationCoordinates
import Langlands.BushnellKutzko.AdjointCentralizer
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Covering simple-character classes: determinant-invariant functionals are scalar -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uK uW

section Elementary

variable {K : Type uK} [Field K] {W : Type uW} [AddCommGroup W] [Module K W]
  {κ : Type*} [Fintype κ] [DecidableEq κ] (β : Module.Basis κ K W)

omit [Fintype κ] in
theorem elementaryEnd_mul_of_ne {k l l' j : κ} (h : l ≠ l') (t s : K) :
    elementaryEnd β k l t * elementaryEnd β l' j s = 0 := by
  apply β.ext
  intro a
  simp only [Module.End.mul_apply, elementaryEnd_apply_basis, LinearMap.zero_apply]
  by_cases hj : j = a
  · simp [hj, map_smul, elementaryEnd_apply_basis, h]
  · simp [hj]

theorem det_one_add_elementaryEnd_of_ne {i j : κ} (hij : i ≠ j) (c : K) :
    LinearMap.det (1 + elementaryEnd β i j c) = 1 := by
  rw [← LinearMap.det_toMatrix β]
  have h : LinearMap.toMatrix β β (1 + elementaryEnd β i j c) = Matrix.transvection i j c := by
    ext a b
    rw [LinearMap.toMatrix_apply, LinearMap.add_apply, Module.End.one_apply,
      elementaryEnd_apply_basis, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases hb : j = b
    · subst hb
      by_cases ha : i = a
      · subst ha
        simp [hij]
      · simp [ha, Finsupp.single_apply, eq_comm]
    · simp only [hb, ite_false, add_zero]
      by_cases hab : a = b
      · subst hab
        simp
      · simp [hab]
  rw [h]
  exact Matrix.det_transvection_of_ne i j hij c

theorem det_one_add_elementaryEnd_self (i : κ) (c : K) :
    LinearMap.det (1 + elementaryEnd β i i c) = 1 + c := by
  rw [← LinearMap.det_toMatrix β]
  have h : LinearMap.toMatrix β β (1 + elementaryEnd β i i c) =
      Matrix.diagonal (fun a => if a = i then 1 + c else 1) := by
    ext a b
    rw [LinearMap.toMatrix_apply, LinearMap.add_apply, Module.End.one_apply,
      elementaryEnd_apply_basis, Matrix.diagonal_apply]
    by_cases hb : i = b
    · subst hb
      by_cases ha : a = i
      · subst ha
        simp
      · simp [ha]
    · by_cases ha : a = b
      · subst ha
        simp [hb, Ne.symm hb]
      · simp [hb, ha]
  rw [h, Matrix.det_diagonal, Finset.prod_ite_eq' Finset.univ i (fun _ => 1 + c)]
  simp

end Elementary

section Generic

variable {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W : Type uW} [AddCommGroup W] [Module K W]

/-- Let `λ` be a function on `End_K(W)` with `λ(0) = 1`, `λ(a + b) = λ(a)λ(b)` and
`λ(ab) = λ(ba)`. If `x ↦ λ(z(x - 1))` on `U^{k+1}` depends only on `det x`, then there is a
scalar `δ ∈ K` with `λ((z - δ)y) = 1` for every `y ∈ 𝔓^{k+1}`. -/
theorem exists_scalar_of_det_invariant (C : LatticeChain 𝒪[K] K W) (k : ℕ)
    (ℓ : Module.End K W → ℂ) (hzero : ℓ 0 = 1) (hadd : ∀ a b, ℓ (a + b) = ℓ a * ℓ b)
    (hcyc : ∀ a b, ℓ (a * b) = ℓ (b * a)) (z : Module.End K W)
    (hdet : ∀ x x' : (Module.End K W)ˣ, x ∈ C.unitFiltration (k + 1) →
      x' ∈ C.unitFiltration (k + 1) →
      LinearMap.det (x : Module.End K W) = LinearMap.det (x' : Module.End K W) →
      ℓ (z * ((x : Module.End K W) - 1)) = ℓ (z * ((x' : Module.End K W) - 1))) :
    ∃ δ : K, ∀ y ∈ C.endFiltration (k + 1), ℓ ((z - scalarEnd δ) * y) = 1 := by
  classical
  have : Nontrivial W := C.nontrivial_space
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨r, β, hβ⟩ := C.exists_basis_splits hϖ
  let i₀ := Classical.choice β.index_nonempty
  let δ := entry β z i₀ i₀
  refine ⟨δ, fun y hy => ?_⟩
  have hneg : ∀ a, ℓ (-a) * ℓ a = 1 := fun a => by rw [← hadd, neg_add_cancel, hzero]
  have hsum : ∀ (s : Finset (Fin r)) (f : Fin r → Module.End K W),
      ℓ (∑ i ∈ s, f i) = ∏ i ∈ s, ℓ (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have hproj (i : Fin r) : elementaryEnd β i i 1 ∈ C.endFiltration 0 :=
    C.elementaryEnd_diag_mem_order hϖ hβ i
  have hentry (i j : Fin r) : elementaryEnd β i j (entry β y i j) ∈ C.endFiltration (k + 1) := by
    rw [← elementaryEnd_mul_mul]
    simpa using C.mul_mem_endFiltration (C.mul_mem_endFiltration (hproj i) hy) (hproj j)
  -- the unit `1 + E_{ij}(c)`
  have hunit (i j : Fin r) (c : K) (hc : elementaryEnd β i j c ∈ C.endFiltration (k + 1)) :
      ∃ g ∈ C.unitFiltration (k + 1),
        (g : Module.End K W) = 1 + elementaryEnd β i j c :=
    C.exists_mem_unitFiltration (n := k + 1) (by omega) (by exact_mod_cast hc)
  have hoff (i j : Fin r) (hij : i ≠ j) (c : K)
      (hc : elementaryEnd β i j c ∈ C.endFiltration (k + 1)) :
      ℓ (z * elementaryEnd β i j c) = 1 := by
    obtain ⟨g, hg, hgv⟩ := hunit i j c hc
    have h := hdet g 1 hg (one_mem _) (by
      rw [hgv, Units.val_one, map_one]
      exact det_one_add_elementaryEnd_of_ne β hij c)
    rw [hgv, add_sub_cancel_left, Units.val_one, sub_self, mul_zero, hzero] at h
    exact h
  have hdiag (i : Fin r) (c : K) (hc : elementaryEnd β i i c ∈ C.endFiltration (k + 1)) :
      ℓ (z * elementaryEnd β i i c) = ℓ (z * elementaryEnd β i₀ i₀ c) := by
    by_cases hc0 : c = 0
    · simp [hc0, elementaryEnd_zero]
    have hc₀ : elementaryEnd β i₀ i₀ c ∈ C.endFiltration (k + 1) := by
      have h1 := (C.elementaryEnd_mem_iff hϖ hβ i i hc0 (k + 1)).mp (by exact_mod_cast hc)
      exact_mod_cast (C.elementaryEnd_mem_iff hϖ hβ i₀ i₀ hc0 (k + 1)).mpr (by omega)
    obtain ⟨g, hg, hgv⟩ := hunit i i c hc
    obtain ⟨g', hg', hgv'⟩ := hunit i₀ i₀ c hc₀
    have h := hdet g g' hg hg' (by
      rw [hgv, hgv', det_one_add_elementaryEnd_self, det_one_add_elementaryEnd_self])
    rwa [hgv, hgv', add_sub_cancel_left, add_sub_cancel_left] at h
  have hscal_comm (i j : Fin r) (c : K) :
      scalarEnd δ * elementaryEnd β i j c = elementaryEnd β i j (δ * c) := by
    apply β.ext
    intro a
    simp [elementaryEnd_apply_basis, scalarEnd, smul_smul]
  have hscal_off (i j : Fin r) (hij : i ≠ j) (c : K) :
      ℓ (scalarEnd δ * elementaryEnd β i j c) = 1 := by
    rw [hscal_comm, show elementaryEnd β i j (δ * c) =
      elementaryEnd β i i 1 * elementaryEnd β i j (δ * c) by rw [elementaryEnd_mul, one_mul],
      hcyc, elementaryEnd_mul_of_ne β (Ne.symm hij), hzero]
  have hscal_diag (i : Fin r) (c : K) :
      ℓ (scalarEnd δ * elementaryEnd β i i c) = ℓ (scalarEnd δ * elementaryEnd β i₀ i₀ c) := by
    rw [hscal_comm, hscal_comm,
      show elementaryEnd β i i (δ * c) =
        elementaryEnd β i i₀ (δ * c) * elementaryEnd β i₀ i 1 by rw [elementaryEnd_mul, mul_one],
      hcyc, elementaryEnd_mul, one_mul]
  have hEc (c : K) : elementaryEnd β i₀ i₀ c = c • elementaryEnd β i₀ i₀ 1 := by
    simp [elementaryEnd]
  have hsand (c : K) : elementaryEnd β i₀ i₀ c * z * elementaryEnd β i₀ i₀ 1 =
      elementaryEnd β i₀ i₀ (c * δ) := by
    rw [hEc, smul_mul_assoc, smul_mul_assoc, elementaryEnd_mul_mul]
    simp [elementaryEnd, smul_smul, δ]
  have hz₀ (c : K) :
      ℓ (z * elementaryEnd β i₀ i₀ c) = ℓ (scalarEnd δ * elementaryEnd β i₀ i₀ c) := by
    rw [show z * elementaryEnd β i₀ i₀ c =
        (z * elementaryEnd β i₀ i₀ 1) * elementaryEnd β i₀ i₀ c by
          rw [mul_assoc, elementaryEnd_mul, one_mul],
      hcyc, ← mul_assoc, hsand, hscal_comm, mul_comm]
  -- decompose `y`
  rw [← sum_elementaryEnd_entry β y, Finset.mul_sum, hsum]
  refine Finset.prod_eq_one (fun i _ => ?_)
  rw [Finset.mul_sum, hsum]
  refine Finset.prod_eq_one (fun j _ => ?_)
  rw [sub_mul, sub_eq_add_neg, hadd, ← neg_mul]
  by_cases hij : i = j
  · subst hij
    have h1 := hdiag i _ (hentry i i)
    rw [hz₀, ← hscal_diag] at h1
    rw [h1, neg_mul, mul_comm]
    exact hneg _
  · rw [hoff i j hij _ (hentry i j), one_mul, neg_mul]
    have := hneg (scalarEnd δ * elementaryEnd β i j (entry β y i j))
    rwa [hscal_off i j hij, mul_one] at this

end Generic

end Langlands.BushnellKutzko
