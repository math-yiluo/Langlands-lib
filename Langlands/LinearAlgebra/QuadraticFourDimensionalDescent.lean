import Langlands.LinearAlgebra.QuadraticNormEquation
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # The norm and discriminant arguments in dimension four -/

noncomputable section

namespace Langlands

open Module LinearMap LinearMap.BilinForm QuadraticMap QuadraticNormEquation
open scoped BigOperators

universe u

/-- Local algebra for dimension four: isotropy after scalar extension to the discriminant algebra
implies isotropy over the field. -/
def QuadraticFourDimensionalDescentStatement : Prop :=
  ∀ {K : Type u} [Field K] [Invertible (2 : K)] {w : Fin 4 → K} {d : K},
    (∏ i, w i) = d → d ≠ 0 →
    (¬ (weightedSumSquares (QuadraticAlgebra K d 0)
      (fun i => algebraMap K (QuadraticAlgebra K d 0) (w i))).Anisotropic) →
    ¬ (weightedSumSquares K w).Anisotropic

namespace QuadraticFourDimensionalDescent

variable {K : Type*} [Field K]

/-- A nontrivial solution of a difference of two binary norms gives a representation of its
multiplier by that binary norm form. -/
theorem exists_eq_of_four_zero [CharZero K] {a b x y z t : K} (ha : a ≠ 0)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b * (z ^ 2 - a * t ^ 2)) :
    ∃ X Y : K, X ^ 2 - a * Y ^ 2 = b := by
  by_cases hs : IsSquare a
  · exact exists_eq_of_isSquare ha hs
  let : Fact (¬ IsSquare a) := ⟨hs⟩
  let left : QuadraticAlgebra K a 0 := ⟨x, y⟩
  let right : QuadraticAlgebra K a 0 := ⟨z, t⟩
  have hnorm : Algebra.norm K left = b * Algebra.norm K right := by
    rw [algebraNorm, algebraNorm]
    exact h
  have hright : right ≠ 0 := by
    intro hz
    have hzero : Algebra.norm K left = 0 := by rw [hnorm, hz, Algebra.norm_zero, mul_zero]
    have hl : left = 0 := Algebra.norm_eq_zero_iff.1 hzero
    have hx : x = 0 := congrArg QuadraticAlgebra.re hl
    have hy : y = 0 := congrArg QuadraticAlgebra.im hl
    have hz' : z = 0 := congrArg QuadraticAlgebra.re hz
    have ht : t = 0 := congrArg QuadraticAlgebra.im hz
    simp [hx, hy, hz', ht] at hne
  let q := left / right
  refine ⟨q.re, q.im, ?_⟩
  rw [← algebraNorm, show q = left * right⁻¹ from div_eq_mul_inv _ _, map_mul, Algebra.norm_inv,
    hnorm, mul_assoc, mul_inv_cancel₀ (fun h0 => hright (Algebra.norm_eq_zero_iff.1 h0)), mul_one]

section OrthogonalBasis

variable {V : Type*} [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) {x : V}

private theorem finrank_orthogonal_line [FiniteDimensional K V] (hx : B x x ≠ 0) :
    finrank K ↥((K ∙ x).orthogonalBilin B) + 1 = finrank K V := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm
  rw [finrank_span_singleton (ne_zero_of_map hx)] at h
  exact h

private def prependOrthogonal {n : ℕ} (hx : B x x ≠ 0)
    (b : Basis (Fin n) K ((K ∙ x).orthogonalBilin B)) : Basis (Fin (n + 1)) K V :=
  Basis.mkFinCons x b (by
    intro c y hy hcy
    rw [add_eq_zero_iff_neg_eq] at hcy
    rw [← hcy, Submodule.neg_mem_iff] at hy
    have hdisj := (isCompl_span_singleton_orthogonal hx).disjoint
    rw [Submodule.disjoint_def] at hdisj
    have h0 := hdisj (c • x) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hy
    exact (smul_eq_zero.1 h0).resolve_right (fun h => hx (h.symm ▸ map_zero _))) (by
    intro y
    refine ⟨-B x y / B x x, fun z hz => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [map_smul, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
      div_mul_cancel₀ _ hx, add_neg_cancel, mul_zero])

private theorem prependOrthogonal_apply {n : ℕ} (hx : B x x ≠ 0)
    (b : Basis (Fin n) K ((K ∙ x).orthogonalBilin B)) :
    (prependOrthogonal B hx b : Fin (n + 1) → V) = Fin.cons x (fun i => (b i : V)) := by
  rw [prependOrthogonal, Basis.coe_mkFinCons]
  rfl

private theorem prependOrthogonal_isOrtho {n : ℕ} (hB : B.IsSymm) (hx : B x x ≠ 0)
    (b : Basis (Fin n) K ((K ∙ x).orthogonalBilin B))
    (hb : (B.domRestrict₁₂ ((K ∙ x).orthogonalBilin B) ((K ∙ x).orthogonalBilin B)).IsOrthoᵢ b) :
    B.IsOrthoᵢ (prependOrthogonal B hx b) := by
  rw [prependOrthogonal_apply]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ]
  · exact (hij rfl).elim
  · exact (b j).prop _ (Submodule.mem_span_singleton_self x)
  · rw [← hB.eq]
    exact (b i).prop _ (Submodule.mem_span_singleton_self x)
  · exact hb (ne_of_apply_ne _ hij)

end OrthogonalBasis

section Discriminant

variable [Invertible (2 : K)]

private theorem exists_orthogonal_basis_of_pair {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hV : finrank K V = 4)
    {x y : V} (hx : B x x ≠ 0) (hy : B y y ≠ 0) (hxy : B x y = 0) :
    ∃ b : Basis (Fin 4) K V, B.IsOrthoᵢ b ∧ b 0 = x ∧ b 1 = y := by
  let W := (K ∙ x).orthogonalBilin B
  let B₁ := B.domRestrict₁₂ W W
  have hmem : y ∈ W := by
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [map_smul, LinearMap.smul_apply, hxy, smul_zero]
  let y₁ : W := ⟨y, hmem⟩
  have hy₁ : B₁ y₁ y₁ ≠ 0 := hy
  let U := (K ∙ y₁).orthogonalBilin B₁
  let B₂ := B₁.domRestrict₁₂ U U
  have hW : finrank K W = 3 := by
    have h := finrank_orthogonal_line B hx
    change finrank K W + 1 = finrank K V at h
    omega
  have hU : finrank K U = 2 := by
    have h := finrank_orthogonal_line B₁ hy₁
    change finrank K U + 1 = finrank K W at h
    omega
  have hB₁ : B₁.IsSymm := hB.domRestrict W
  have hB₂ : B₂.IsSymm := hB₁.domRestrict U
  obtain ⟨v, hv⟩ := exists_orthogonal_basis hB₂
  let e := finCongr hU
  let b₂ : Basis (Fin 2) K U := v.reindex e
  have hb₂ : B₂.IsOrthoᵢ b₂ := by
    intro i j hij
    change B₂ (b₂ i) (b₂ j) = 0
    simp only [b₂, Basis.reindex_apply]
    exact hv (fun he => hij (e.symm.injective he))
  let b₁ : Basis (Fin 3) K W := prependOrthogonal B₁ hy₁ b₂
  let b : Basis (Fin 4) K V := prependOrthogonal B hx b₁
  refine ⟨b, prependOrthogonal_isOrtho B hB hx b₁
    (prependOrthogonal_isOrtho B₁ hB₁ hy₁ b₂ hb₂), ?_, ?_⟩
  · exact congrFun (prependOrthogonal_apply B hx b₁) 0
  · refine (congrFun (prependOrthogonal_apply B hx b₁) 1).trans ?_
    exact congrArg Subtype.val (congrFun (prependOrthogonal_apply B₁ hy₁ b₂) 0)

private theorem discr_of_orthogonal_basis {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (q : QuadraticForm K V) (b : Basis ι K V)
    (hb : q.associated.IsOrthoᵢ b) : q.discr b = ∏ i, q (b i) := by
  have hmatrix : q.toMatrix b = Matrix.diagonal (fun i => q (b i)) := by
    ext i j
    rw [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply]
    by_cases h : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, QuadraticMap.associated_eq_self_apply]
    · rw [Matrix.diagonal_apply_ne _ h, hb h]
  rw [QuadraticForm.discr, hmatrix, Matrix.det_diagonal]

/-- In dimension four, an orthogonal pair whose nonzero values have ratio minus the
basis discriminant forces isotropy. -/
private theorem not_anisotropic_of_orthogonal_pair {V : Type*} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (b₀ : Basis (Fin 4) K V) {d : K} (hd : q.discr b₀ = d)
    (hd₀ : d ≠ 0) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : q.associated x y = 0)
    (hvals : q x + d * q y = 0) : ¬ q.Anisotropic := by
  classical
  intro han
  let : FiniteDimensional K V := Module.Finite.of_basis b₀
  have hV : finrank K V = 4 := by rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hxq : q x ≠ 0 := fun h => hx (han x h)
  have hyq : q y ≠ 0 := fun h => hy (han y h)
  obtain ⟨b, hb, hbx, hby⟩ := exists_orthogonal_basis_of_pair q.associated
    (QuadraticForm.associated_isSymm K q) hV
    (by simpa only [QuadraticMap.associated_eq_self_apply] using hxq)
    (by simpa only [QuadraticMap.associated_eq_self_apply] using hyq) hxy
  let δ := (LinearMap.toMatrix b b₀ (LinearMap.id : V →ₗ[K] V)).det
  have hprod : q.discr b = δ * δ * d := by
    have hid : q.comp (LinearMap.id : V →ₗ[K] V) = q := by ext v; rfl
    simpa only [hid, hd] using
      QuadraticForm.discr_comp (b := b) b₀ q (LinearMap.id : V →ₗ[K] V)
  rw [discr_of_orthogonal_basis q b hb, Fin.prod_univ_four, hbx, hby] at hprod
  have hxval : q x = -(d * q y) := by linear_combination hvals
  rw [hxval] at hprod
  have hsquare : -(q (b 2) * q (b 3)) * q y ^ 2 = δ ^ 2 := by
    apply mul_right_cancel₀ hd₀
    linear_combination hprod
  have h3 : q (b 3) ≠ 0 := fun h => b.ne_zero 3 (han _ h)
  let s := δ / (q y * q (b 3))
  have hval : q (b 2) + s ^ 2 * q (b 3) = 0 := by
    dsimp only [s]
    field_simp [hyq, h3]
    linear_combination -hsquare
  let v := b 2 + s • b 3
  have hv : v ≠ 0 := by
    intro h
    have hrep := congrArg (fun w => b.repr w 2) h
    simp [v] at hrep
  have hortho : q.IsOrtho (b 2) (s • b 3) := by
    apply QuadraticMap.associated_isOrtho.1
    rw [map_smul, hb (by decide : (2 : Fin 4) ≠ 3), smul_zero]
  have hq : q v = 0 := by
    change q (b 2 + s • b 3) = 0
    rw [QuadraticMap.isOrtho_def] at hortho
    rw [hortho, QuadraticMap.map_smul, smul_eq_mul, ← pow_two]
    exact hval
  exact hv (han v hq)

private theorem discr_weightedSumSquares {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → K) :
    QuadraticForm.discr (Pi.basisFun K ι) (weightedSumSquares K w) = ∏ i, w i := by
  let q : QuadraticForm K (ι → K) := weightedSumSquares K w
  change q.discr (Pi.basisFun K ι) = _
  have horth : q.associated.IsOrthoᵢ (Pi.basisFun K ι) := by
    intro i j hij
    change q.associated (Pi.basisFun K ι i) (Pi.basisFun K ι j) = 0
    rw [QuadraticMap.associated_isOrtho, QuadraticMap.isOrtho_def]
    simp only [q, weightedSumSquares_apply, smul_eq_mul, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hki]
      · simp [hki, hkj]
  rw [discr_of_orthogonal_basis q (Pi.basisFun K ι) horth]
  apply Finset.prod_congr rfl
  intro i _
  simp only [q, weightedSumSquares_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne
    simp [hne]
  · simp

end Discriminant

/-- A four-dimensional diagonal form isotropic over its discriminant algebra is isotropic
already over the field, provided its discriminant is nonzero. -/
theorem diagonal_not_anisotropic_of_discriminant_extension :
    QuadraticFourDimensionalDescentStatement.{u} := by
  intro K _ _ w d hd hd₀ h han
  let q := weightedSumSquares K w
  obtain ⟨z, hne, hz⟩ := (not_anisotropic_iff_exists _).1 h
  let x : Fin 4 → K := fun i => (z i).re
  let y : Fin 4 → K := fun i => (z i).im
  have hreal := congrArg QuadraticAlgebra.re hz
  have himag := congrArg QuadraticAlgebra.im hz
  simp only [weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_four,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero, mul_zero, zero_mul, add_zero] at hreal himag
  have hvals : q x + d * q y = 0 := by
    simp only [q, x, y, weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_four]
    linear_combination hreal
  have horth : q.associated x y = 0 := by
    rw [QuadraticMap.associated_isOrtho, QuadraticMap.isOrtho_def]
    simp only [q, x, y, weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_four, Pi.add_apply]
    linear_combination himag
  have hpair : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨hx, hy⟩
    apply hne
    funext i
    apply QuadraticAlgebra.ext
    · exact congrFun hx i
    · exact congrFun hy i
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero, zero_add] at hvals
    exact hpair ⟨hx, han y ((mul_eq_zero.mp hvals).resolve_left hd₀)⟩
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, map_zero, mul_zero, add_zero] at hvals
    exact hpair ⟨han x hvals, hy⟩
  exact not_anisotropic_of_orthogonal_pair q (Pi.basisFun K (Fin 4))
    ((discr_weightedSumSquares w).trans hd) hd₀ hx hy horth hvals han

end QuadraticFourDimensionalDescent

end Langlands
