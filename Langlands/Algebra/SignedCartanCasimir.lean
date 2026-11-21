import Langlands.Algebra.LieCasimir
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Signed Casimir elements adapted to a Cartan involution

For a finite-dimensional real Lie algebra with an invariant symmetric bilinear form `B` and a
linear involution `s` preserving `B` such that `B x (s x) > 0` for `x ≠ 0`, the `+1` and `-1`
eigenspaces of `s` have bases that are orthonormal for `B` and `-B` respectively. The resulting
Casimir element of `B` is a signed sum of squares, central in the complex enveloping algebra.
-/

noncomputable section

universe u

open Module
open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Algebra.SignedCartanCasimir

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℝ L]

/-- A positive definite symmetric form restricted to a subspace has an orthonormal basis. -/
theorem exists_orthonormal_basis_of_pos [FiniteDimensional ℝ L]
    (Q : LinearMap.BilinForm ℝ L) (hsymm : ∀ x y, Q x y = Q y x) (S : Submodule ℝ L)
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < Q x x) :
    ∃ (m : ℕ) (b : Basis (Fin m) ℝ S), ∀ i j,
      Q (b i) (b j) = if i = j then 1 else 0 := by
  classical
  let Q' := Q.restrict S
  have hQ : Q'.IsSymm := ⟨fun x y => hsymm x y⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hQ)
  have hpos' (i : Fin (finrank ℝ S)) : 0 < Q' (b i) (b i) :=
    hpos _ (b i).2 (fun h => b.ne_zero i (Subtype.ext h))
  let c : Fin (finrank ℝ S) → ℝ := fun i => (Real.sqrt (Q' (b i) (b i)))⁻¹
  have hc (i : Fin (finrank ℝ S)) : IsUnit (c i) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hpos' i))))
  refine ⟨finrank ℝ S, b.isUnitSMul hc, ?_⟩
  intro i j
  change Q' ((b.isUnitSMul hc) i) ((b.isUnitSMul hc) j) = _
  rw [Basis.isUnitSMul_apply, Basis.isUnitSMul_apply]
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    dsimp [c]
    have hs := Real.sq_sqrt (le_of_lt (hpos' i))
    have hn : Real.sqrt (Q' (b i) (b i)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hpos' i))
    field_simp
    nlinarith
  · rw [ite_eq_right hij, hb hij]
    simp

/-- The real Lie algebra maps to the complex enveloping algebra of its complexification. -/
def realGenerator :
    L →ₗ⁅ℝ⁆ UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) :=
  { ((UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] L)).toLinearMap.restrictScalars ℝ).comp
      (TensorProduct.mk ℝ ℂ L 1) with
    map_lie' := by
      intro x y
      change UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆) =
        ⁅UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] x),
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] y)⁆
      rw [← (UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] L)).map_lie,
        LieAlgebra.ExtendScalars.bracket_tmul, one_mul] }

@[simp]
theorem realGenerator_apply (x : L) :
    realGenerator x = UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) := rfl

theorem ι_tmul (z : ℂ) (x : L) :
    UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] x) =
      z • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- An element commuting with the images of all real directions is central. -/
theorem mem_center_of_commute_real
    (a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))
    (ha : ∀ x : L, realGenerator x * a = a * realGenerator x) :
    a ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) := by
  let S := Subalgebra.centralizer ℂ {a}
  have hreal (x : L) : realGenerator x ∈ S := by
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (ha x).symm
  have hcomplex (x : ℂ ⊗[ℝ] L) : UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    induction x using TensorProduct.inductionOn with
    | tmul z x =>
      rw [ι_tmul]
      exact S.smul_mem (hreal x) z
    | add x y hx hy =>
      simpa only [map_add] using S.add_mem hx hy
  have hle : Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ℂ ⊗[ℝ] L → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact hcomplex x
  rw [Subalgebra.mem_center_iff]
  intro c
  have hc : c ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ℂ ⊗[ℝ] L → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle hc) _ (Set.mem_singleton _)).symm

/-- A signed sum of squares is the full sum minus twice the negative part. -/
theorem sum_signed_eq {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : Finset (Fin n)) (g : Fin n → M) :
    (∑ i, (if i ∈ J then (-1 : ℂ) else 1) • g i) = ∑ i, g i - (2 : ℂ) • ∑ j ∈ J, g j := by
  classical
  have hterm (i : Fin n) : (if i ∈ J then (-1 : ℂ) else 1) • g i =
      g i - (2 : ℂ) • (if i ∈ J then g i else 0) := by
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi, ite_eq_left hi, two_smul]
      simp only [neg_smul, one_smul]
      abel
    · rw [ite_eq_right hi, ite_eq_right hi]
      simp
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_ite_mem, Finset.univ_inter]

section Signed

variable [FiniteDimensional ℝ L]

/-- **Signed Cartan Casimir.** If `B` is a symmetric invariant form on a finite-dimensional real
Lie algebra and `s` is a `B`-preserving linear involution with `B x (s x) > 0` for `x ≠ 0`, then
there is a basis `X` of `L` and a set `J` of indices of `-1` eigenvectors of `s` such that
`∑ i, X i ^ 2 - 2 • ∑ j ∈ J, X j ^ 2` is central in the complex enveloping algebra. -/
theorem exists_signed_casimir
    (B : LinearMap.BilinForm ℝ L) (hsymm : ∀ x y, B x y = B y x)
    (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (s : L →ₗ[ℝ] L) (hs : ∀ x, s (s x) = x) (hBs : ∀ x y, B (s x) (s y) = B x y)
    (hpos : ∀ x, x ≠ 0 → 0 < B x (s x)) :
    ∃ (n : ℕ) (X : Fin n → L) (J : Finset (Fin n)),
      Submodule.span ℝ (Set.range X) = ⊤ ∧ (∀ j ∈ J, s (X j) = -X j) ∧
      (∑ i, UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] X i) ^ 2 -
        (2 : ℂ) • ∑ j ∈ J, UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] L)
          ((1 : ℂ) ⊗ₜ[ℝ] X j) ^ 2) ∈
        Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) := by
  classical
  -- the two eigenspaces
  let P : Submodule ℝ L := LinearMap.ker (s - LinearMap.id)
  let K : Submodule ℝ L := LinearMap.ker (s + LinearMap.id)
  have hP (x : L) : x ∈ P ↔ s x = x := by
    change (s - LinearMap.id : L →ₗ[ℝ] L) x = 0 ↔ _
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hK (x : L) : x ∈ K ↔ s x = -x := by
    change (s + LinearMap.id : L →ₗ[ℝ] L) x = 0 ↔ _
    rw [LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hPK : IsCompl P K := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxP hxK
      have h1 := (hP x).mp hxP
      have h2 := (hK x).mp hxK
      have h3 : (2 : ℝ) • x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        rw [h2, neg_add_cancel]
      exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x = (2 : ℝ)⁻¹ • (x + s x) + (2 : ℝ)⁻¹ • (x - s x) := by
        rw [← smul_add]
        rw [show x + s x + (x - s x) = (2 : ℝ) • x by rw [two_smul]; abel]
        rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [hx]
      apply Submodule.add_mem_sup
      · rw [hP, map_smul, map_add, hs, add_comm]
      · rw [hK, map_smul, map_sub, hs, ← smul_neg, neg_sub]
  have hposP : ∀ x ∈ P, x ≠ 0 → 0 < B x x := by
    intro x hx hx0
    have := hpos x hx0
    rwa [(hP x).mp hx] at this
  have hposK : ∀ x ∈ K, x ≠ 0 → 0 < (-B) x x := by
    intro x hx hx0
    have := hpos x hx0
    rw [(hK x).mp hx, LinearMap.BilinForm.neg_right] at this
    simpa using this
  have hsymmK : ∀ x y, (-B) x y = (-B) y x := by
    intro x y
    simp only [LinearMap.neg_apply, hsymm x y]
  obtain ⟨p, bP, hbP⟩ := exists_orthonormal_basis_of_pos B hsymm P hposP
  obtain ⟨k, bK, hbK⟩ := exists_orthonormal_basis_of_pos (-B) hsymmK K hposK
  have horth (x y : L) (hx : x ∈ P) (hy : y ∈ K) : B x y = 0 := by
    have h := hBs x y
    rw [(hP x).mp hx, (hK y).mp hy, LinearMap.BilinForm.neg_right] at h
    have h2 : (2 : ℝ) * B x y = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  -- the adapted basis
  let e : (P × K) ≃ₗ[ℝ] L := Submodule.prodEquivOfIsCompl P K hPK
  let b0 : Basis (Fin p ⊕ Fin k) ℝ L := (bP.prod bK).map e
  have hb0l (i : Fin p) : b0 (Sum.inl i) = (bP i : L) := by
    simp [b0, e, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hb0r (i : Fin k) : b0 (Sum.inr i) = (bK i : L) := by
    simp [b0, e, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  let b : Basis (Fin (p + k)) ℝ L := b0.reindex finSumFinEquiv
  let J : Finset (Fin (p + k)) := Finset.univ.filter fun i => (finSumFinEquiv.symm i).isRight
  let ε : Fin (p + k) → ℝ := fun i => if i ∈ J then -1 else 1
  have hJ (σ : Fin p ⊕ Fin k) : finSumFinEquiv σ ∈ J ↔ σ.isRight := by
    simp [J]
  have hb (σ : Fin p ⊕ Fin k) : b (finSumFinEquiv σ) = b0 σ := by
    simp only [b, Basis.reindex_apply, Equiv.symm_apply_apply]
  have hpair (i j : Fin (p + k)) : B (b i) (b j) = if i = j then ε i else 0 := by
    obtain ⟨σ, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨τ, rfl⟩ := finSumFinEquiv.surjective j
    simp only [hb, ε, hJ, finSumFinEquiv.injective.eq_iff]
    rcases σ with σ | σ <;> rcases τ with τ | τ
    · rw [hb0l, hb0l]
      simpa [Sum.inl.injEq] using hbP σ τ
    · rw [hb0l, hb0r, horth _ _ (bP σ).2 (bK τ).2]
      simp
    · rw [hb0r, hb0l, hsymm, horth _ _ (bP τ).2 (bK σ).2]
      simp
    · rw [hb0r, hb0r]
      have := hbK σ τ
      simp only [LinearMap.neg_apply] at this
      by_cases h : σ = τ
      · subst h
        simp only [↓reduceIte] at this
        simp only [↓reduceIte, Sum.isRight_inr]
        linarith
      · rw [ite_eq_right h] at this
        simp only [Sum.inr.injEq, h, ↓reduceIte]
        linarith
  have hε (i : Fin (p + k)) : ε i * ε i = 1 := by
    simp only [ε]
    split_ifs <;> norm_num
  have hB : B.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · by_contra hx0
      have h := hpos x hx0
      rw [hx (s x)] at h
      exact lt_irrefl _ h
    · by_contra hy0
      have h := hpos y hy0
      rw [hsymm, hy (s y)] at h
      exact lt_irrefl _ h
  have hdual (i : Fin (p + k)) : B.dualBasis hB b i = ε i • b i := by
    apply (B.dualBasis hB b).repr.injective
    ext j
    rw [Basis.repr_self, LinearMap.BilinForm.dualBasis_repr_apply,
      LinearMap.BilinForm.smul_left, hpair, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp [hε]
    · simp [h]
  -- the Casimir
  let f := realGenerator (L := L)
  have hcas : Langlands.Algebra.LieCasimir.casimirImage B hB b f =
      ∑ i, (if i ∈ J then (-1 : ℂ) else 1) •
        UniversalEnvelopingAlgebra.ι ℂ (L := ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] b i) ^ 2 := by
    unfold Langlands.Algebra.LieCasimir.casimirImage
    apply Finset.sum_congr rfl
    intro i _
    rw [hdual, map_smul, realGenerator_apply, mul_smul_comm, pow_two]
    by_cases hi : i ∈ J
    · simp only [ε, hi, ↓reduceIte, neg_one_smul]
    · simp only [ε, hi, ↓reduceIte, one_smul]
  refine ⟨p + k, b, J, b.span_eq, ?_, ?_⟩
  · intro j hj
    obtain ⟨σ, rfl⟩ := finSumFinEquiv.surjective j
    have hj' : σ.isRight := (hJ σ).mp hj
    rw [hb]
    rcases σ with σ | σ
    · simp at hj'
    · rw [hb0r]
      exact (hK _).mp (bK σ).2
  · rw [← sum_signed_eq J, ← hcas]
    apply mem_center_of_commute_real
    intro x
    exact Langlands.Algebra.LieCasimir.casimirImage_commutes_generator B hB hInv b f x

end Signed

end Langlands.Algebra.SignedCartanCasimir
