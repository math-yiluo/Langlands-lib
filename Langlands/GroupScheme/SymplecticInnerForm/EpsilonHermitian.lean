import Langlands.GroupScheme.Quaternionic.Involution
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Prod

/-!
# `ε`-symmetric elements of algebras with involution

For an involution of the first kind `θ` of a `K`-algebra `R` and a scalar `ε`, this module
studies the `ε`-symmetric elements `{x | θ x = ε • x}`. It proves:

* transport of involutions along algebra isomorphisms;
* if `τ = Int(H) ∘ θ` for a unit `H` with `θ H = ε • H` and `ε * ε = 1`, left multiplication
  by `H` identifies the `ε`-symmetric elements of `θ` with the symmetric elements of `τ`;
* the dimension of the `ε`-hermitian matrices `{z | ᵗz^θ = ε • z}` of `M_ι(R)`:
  `card ι * dim (θ-ε-symmetric) + (card ι choose 2) * dim R`;
* away from characteristic two, symmetric and skew elements have complementary dimensions.
-/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

section Ring

variable {K : Type u} {R : Type v} [CommRing K] [Ring R] [Algebra K R]
  (θ : FirstKindInvolution K R)

/-- The `ε`-symmetric elements `{x | θ x = ε • x}` of an involution of the first kind. -/
def epsSymmetric (ε : K) : Submodule K R :=
  LinearMap.ker (θ.toLinearMap - ε • LinearMap.id)

theorem mem_epsSymmetric {ε : K} {x : R} : x ∈ θ.epsSymmetric ε ↔ θ x = ε • x := by
  simp [epsSymmetric, sub_eq_zero]

theorem epsSymmetric_one : θ.epsSymmetric 1 = θ.symmetricSubspace := by
  ext x
  simp [mem_epsSymmetric, mem_symmetricSubspace]

/-- Transport of an involution of the first kind along an algebra isomorphism:
`x ↦ φ (θ (φ⁻¹ x))`. -/
def algEquivCongr {B : Type w} [Ring B] [Algebra K B] (φ : R ≃ₐ[K] B) :
    FirstKindInvolution K B where
  toLinearMap := φ.toLinearMap ∘ₗ θ.toLinearMap ∘ₗ φ.symm.toLinearMap
  map_one' := by simp
  map_mul' x y := by simp
  involutive' x := by simp

@[simp] theorem algEquivCongr_apply {B : Type w} [Ring B] [Algebra K B] (φ : R ≃ₐ[K] B)
    (x : B) : θ.algEquivCongr φ x = φ (θ (φ.symm x)) :=
  rfl

theorem algEquivCongr_apply_map {B : Type w} [Ring B] [Algebra K B] (φ : R ≃ₐ[K] B)
    (x : R) : θ.algEquivCongr φ (φ x) = φ (θ x) := by
  simp

/-- An algebra isomorphism identifies the `ε`-symmetric elements of `θ` with those of the
transported involution. -/
def epsSymmetricCongr {B : Type w} [Ring B] [Algebra K B] (φ : R ≃ₐ[K] B) (ε : K) :
    θ.epsSymmetric ε ≃ₗ[K] (θ.algEquivCongr φ).epsSymmetric ε :=
  φ.toLinearEquiv.ofSubmodules _ _ (by
    ext y
    simp only [Submodule.mem_map, mem_epsSymmetric, algEquivCongr_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp [hx]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      apply φ.injective
      simpa using hy)

/-- If `θ H = ε • H` for a unit `H` with inverse `H'`, then also `θ H' = ε • H'`, provided
`ε * ε = 1`. -/
theorem map_gram_inv {ε : K} (hε : ε * ε = 1) {H H' : R} (hHH' : H * H' = 1)
    (hθH : θ H = ε • H) : θ H' = ε • H' := by
  have h1 : θ H' * θ H = 1 := by rw [← map_mul, hHH', map_one]
  have h2 : ε • (θ H' * H) = 1 := by rw [hθH, mul_smul_comm] at h1; exact h1
  have h3 : ε • θ H' = H' := by
    calc ε • θ H' = ε • (θ H' * H) * H' := by
          rw [smul_mul_assoc, mul_assoc, hHH', mul_one]
      _ = H' := by rw [h2, one_mul]
  calc θ H' = (ε * ε) • θ H' := by rw [hε, one_smul]
    _ = ε • H' := by rw [mul_smul, h3]

/-- Let `τ = Int(H) ∘ θ`, that is `τ y = H * θ y * H'` with `H * H' = 1 = H' * H`, where
`θ H = ε • H` and `ε * ε = 1`. Then `z ↦ H * z` identifies the `ε`-symmetric elements of
`θ` with the symmetric elements of `τ`. -/
def gramEquiv (τ : FirstKindInvolution K R) {ε : K} (hε : ε * ε = 1) {H H' : R}
    (hHH' : H * H' = 1) (hH'H : H' * H = 1) (hθH : θ H = ε • H)
    (hτ : ∀ y, τ y = H * θ y * H') :
    θ.epsSymmetric ε ≃ₗ[K] τ.symmetricSubspace where
  toFun z := ⟨H * z, by
    rw [mem_symmetricSubspace, hτ, map_mul, (θ.mem_epsSymmetric).1 z.2, hθH,
      smul_mul_smul_comm, hε, one_smul, mul_assoc, mul_assoc, hHH', mul_one]⟩
  map_add' x y := by
    ext
    simp [mul_add]
  map_smul' c x := by
    ext
    simp
  invFun y := ⟨H' * y, by
    rw [mem_epsSymmetric, map_mul, θ.map_gram_inv hε hHH' hθH, mul_smul_comm]
    have hy : τ (y : R) = y := (τ.mem_symmetricSubspace).1 y.2
    rw [hτ] at hy
    congr 1
    calc θ (y : R) * H' = H' * (H * θ y * H') := by
          rw [← mul_assoc, ← mul_assoc, hH'H, one_mul]
      _ = H' * y := by rw [hy]⟩
  left_inv z := by
    ext
    simp [← mul_assoc, hH'H]
  right_inv y := by
    ext
    simp [← mul_assoc, hHH']

theorem finrank_symmetricSubspace_eq_of_gram [Module.Free K R] [Module.Finite K R]
    (τ : FirstKindInvolution K R) {ε : K} (hε : ε * ε = 1) {H H' : R}
    (hHH' : H * H' = 1) (hH'H : H' * H = 1) (hθH : θ H = ε • H)
    (hτ : ∀ y, τ y = H * θ y * H') :
    Module.finrank K τ.symmetricSubspace = Module.finrank K (θ.epsSymmetric ε) :=
  (θ.gramEquiv τ hε hHH' hH'H hθH hτ).finrank_eq.symm

end Ring

section Matrix

variable {K : Type u} {R : Type v} [Field K] [Ring R] [Algebra K R]
  (θ : FirstKindInvolution K R)

/-- The coordinates of an `ε`-hermitian matrix `z` (`ᵗz^θ = ε • z`) for a linear order of
the index type: its diagonal, which is `ε`-symmetric, and its strictly upper triangular
part, which is arbitrary. -/
def hermCoordEquiv (ι : Type w) [Fintype ι] [LinearOrder ι] {ε : K} (hε : ε * ε = 1) :
    (θ.matrix ι).epsSymmetric ε ≃ₗ[K]
      (ι → θ.epsSymmetric ε) × ({p : ι × ι // p.1 < p.2} → R) where
  toFun z := (fun i => ⟨(z : Matrix ι ι R) i i, by
      have hz := congrFun (congrFun (((θ.matrix ι).mem_epsSymmetric).1 z.2) i) i
      simpa [mem_epsSymmetric] using hz⟩,
    fun p => (z : Matrix ι ι R) p.1.1 p.1.2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp
  invFun st := ⟨Matrix.of fun i j =>
      if h : i < j then st.2 ⟨(i, j), h⟩
      else if h' : j < i then ε • θ (st.2 ⟨(j, i), h'⟩) else (st.1 i : R), by
    rw [mem_epsSymmetric]
    ext i j
    simp only [matrix_apply, Matrix.of_apply, Matrix.smul_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [dite_eq_right (lt_asymm hij), dite_eq_left hij, dite_eq_left hij, map_smul, apply_apply]
    · simp only [lt_irrefl, dite_eq_right, not_false_eq_true]
      exact (θ.mem_epsSymmetric).1 (st.1 i).2
    · rw [dite_eq_left hji, dite_eq_right (lt_asymm hji), dite_eq_left hji, smul_smul, hε,
        one_smul]⟩
  left_inv z := by
    have hz := ((θ.matrix ι).mem_epsSymmetric).1 z.2
    ext i j
    simp only [Matrix.of_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [dite_eq_left hij]
    · simp
    · rw [dite_eq_right (lt_asymm hji), dite_eq_left hji]
      have := congrFun (congrFun hz i) j
      simp only [matrix_apply, Matrix.smul_apply] at this
      rw [this, smul_smul, hε, one_smul]
  right_inv st := by
    ext i
    · simp
    · simp [dite_eq_left i.2]

theorem finrank_epsSymmetric_matrix [FiniteDimensional K R] (ι : Type w) [Fintype ι]
    [DecidableEq ι] {ε : K} (hε : ε * ε = 1) :
    Module.finrank K ((θ.matrix ι).epsSymmetric ε) =
      Fintype.card ι * Module.finrank K (θ.epsSymmetric ε) +
        (Fintype.card ι).choose 2 * Module.finrank K R := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have h := (θ.hermCoordEquiv ι hε).finrank_eq
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have hc : Fintype.card {p : ι × ι // p.1 < p.2} = (Fintype.card ι).choose 2 := by
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt]
  rw [hc] at h
  convert h

/-- Away from characteristic two, the symmetric and skew-symmetric elements have
complementary dimensions. -/
theorem finrank_symmetricSubspace_add_finrank_skew [FiniteDimensional K R]
    (h2 : (2 : K) ≠ 0) :
    Module.finrank K θ.symmetricSubspace + Module.finrank K (θ.epsSymmetric (-1)) =
      Module.finrank K R := by
  have hinf : θ.symmetricSubspace ⊓ θ.epsSymmetric (-1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_symmetricSubspace, mem_epsSymmetric] at hx
    have hxx : (2 : K) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hx.1]
      rw [hx.2, neg_one_smul, neg_add_cancel]
    rw [Submodule.mem_bot]
    calc x = (2 : K)⁻¹ • (2 : K) • x := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hxx, smul_zero]
  have hsup : θ.symmetricSubspace ⊔ θ.epsSymmetric (-1) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = (2 : K)⁻¹ • (x + θ x) + (2 : K)⁻¹ • (x - θ x) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul K x, smul_smul, inv_mul_cancel₀ h2,
        one_smul]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_symmetricSubspace, map_smul, map_add, apply_apply, add_comm]
    · rw [mem_epsSymmetric, map_smul, map_sub, apply_apply, smul_comm, neg_one_smul, neg_sub]
  have h := Submodule.finrank_sup_add_finrank_inf_eq θ.symmetricSubspace (θ.epsSymmetric (-1))
  rw [hsup, hinf, finrank_top, finrank_bot, add_zero] at h
  exact h.symm

end Matrix

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
