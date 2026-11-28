import Langlands.GroupScheme.Quaternionic.QuaternionicSplitOppositeValues
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Isotropic skew rows with an invertible split quaternion coordinate -/

noncomputable section

open Matrix Module

universe u v

namespace Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false

section IsotropicProjection

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

private theorem HyperbolicPair.exists_isotropic_map_ne_zero
    (P : HyperbolicPair B) (hs : B.IsSymm) (h2 : (2 : K) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : f ≠ 0) : ∃ x, B x x = 0 ∧ f x ≠ 0 := by
  by_contra! h
  have hx := h P.x P.xx
  have hy := h P.y P.yy
  have hw (w : P.orthogonalComplement) : f (w : V) = 0 := by
    let a := -(B w w) / 2
    let r := P.split hs ((1, a), w)
    have hr : B r r = 0 := by
      rw [P.split_pairing]
      simp only [one_mul, mul_one]
      dsimp only [a]
      field_simp
      ring
    simpa only [r, P.split_apply, map_add, map_smul, hx, hy, smul_zero, add_zero, zero_add] using h r hr
  apply hf
  ext v
  obtain ⟨⟨⟨a, b⟩, w⟩, rfl⟩ := (P.split hs).surjective v
  simp only [P.split_apply, map_add, map_smul, hx, hy, hw, smul_zero, add_zero, LinearMap.zero_apply]

variable [FiniteDimensional K V]

/-- A nondegenerate symmetric space of dimension at least eight over a field
with quadratic anisotropic dimension at most four has a totally isotropic
plane mapping isomorphically to any prescribed two-dimensional quotient. -/
theorem exists_isotropic_pair_of_surjective_projection
    (h2 : (2 : K) ≠ 0) (hs : B.IsSymm) (hB : B.Nondegenerate) (hn : 8 ≤ finrank K V)
    (his : ∀ (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (Q : QuadraticForm K U), 4 < finrank K U → ∃ z, z ≠ 0 ∧ Q z = 0)
    (p : V →ₗ[K] (Fin 2 → K)) (hp : Function.Surjective p) :
    ∃ x y, B x x = 0 ∧ B x y = 0 ∧ B y y = 0 ∧
      p x 0 * p y 1 - p x 1 * p y 0 ≠ 0 := by
  obtain ⟨r, hr, hrr⟩ := his V B.toQuadraticMap (by omega)
  obtain ⟨P, _⟩ := HyperbolicPair.exists_with_first hs hB h2 r hr hrr
  have hV := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hV
  have hker : LinearMap.ker p ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hV
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hp0 : p ≠ 0 := fun h => by
    subst p
    obtain ⟨w, hw⟩ := hp (1 : Fin 2 → K)
    exact zero_ne_one (congrFun hw 0)
  have hBz : B z ≠ 0 := fun h => hz0 (hB.1 z fun w => DFunLike.congr_fun h w)
  obtain ⟨x₀, h₀, hp₀⟩ := P.exists_isotropic_map_ne_zero hs h2 p hp0
  obtain ⟨x₁, h₁, hz₁⟩ := P.exists_isotropic_map_ne_zero hs h2 (B z) hBz
  have hx₁ : B x₁ z ≠ 0 := (hs.eq x₁ z).trans_ne hz₁
  obtain ⟨x, hxx, hpx, w, hpw, hxw⟩ :
      ∃ x, B x x = 0 ∧ p x ≠ 0 ∧ ∃ w, p w = 0 ∧ B x w ≠ 0 := by
    by_cases h : p x₁ = 0
    · by_cases h₀₁ : B x₀ x₁ = 0
      · by_cases h₀z : B x₀ z = 0
        · refine ⟨x₀ + x₁, ?_, ?_, z, hz, ?_⟩
          · have h₁₀ := (hs.eq x₁ x₀).trans h₀₁
            simp only [map_add, LinearMap.add_apply, h₀, h₁, h₀₁, h₁₀, add_zero]
          · simpa only [map_add, h, add_zero] using hp₀
          · simpa only [map_add, LinearMap.add_apply, h₀z, zero_add] using hx₁
        · exact ⟨x₀, h₀, hp₀, z, hz, h₀z⟩
      · exact ⟨x₀, h₀, hp₀, x₁, h, h₀₁⟩
    · exact ⟨x₁, h₁, h, z, hz, hx₁⟩
  have hx : x ≠ 0 := fun h => hpx (h.symm ▸ p.map_zero)
  obtain ⟨Q, hxQ⟩ := HyperbolicPair.exists_with_first hs hB h2 x hx hxx
  let f : (Fin 2 → K) →ₗ[K] K := p x 0 • LinearMap.proj 1 - p x 1 • LinearMap.proj 0
  have hf (t : Fin 2 → K) : f t = p x 0 * t 1 - p x 1 * t 0 := rfl
  have hfx : f (p x) = 0 := by rw [hf, mul_comm (p x 0), sub_self]
  have hfn : f ≠ 0 := by
    intro h
    apply hpx
    funext i
    have he (j : Fin 2) : f (Pi.single j 1) = 0 := DFunLike.congr_fun h _
    fin_cases i
    · simpa [hf, Pi.single_apply] using he 1
    · simpa [hf, Pi.single_apply] using he 0
  obtain ⟨t, htn⟩ : ∃ t : Fin 2 → K, f t ≠ 0 := by
    by_contra! h
    exact hfn (LinearMap.ext h)
  obtain ⟨s, hst⟩ := hp t
  let a := s - (B x s / B x w) • w
  have hap : p a = t := by simp [a, hpw, hst]
  have hax : B x a = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hxw, sub_self]
  let U := Q.orthogonalComplement
  let C := B.restrict U
  have hC : C.IsSymm := ⟨fun b c => hs.eq (b : V) c⟩
  have hUn : 4 < finrank K U := by
    have hdim := (Q.split hs).finrank_eq
    simp only [finrank_prod, finrank_self] at hdim
    change 1 + 1 + finrank K U = finrank K V at hdim
    omega
  obtain ⟨b, hb, hbb⟩ := his U C.toQuadraticMap hUn
  obtain ⟨T, _⟩ := HyperbolicPair.exists_with_first hC (Q.nondegenerate_restrict hs hB) h2 b hb hbb
  let g := f.comp (p.comp U.subtype)
  have hgn : g ≠ 0 := by
    intro h
    apply htn
    let c := ((Q.split hs).symm a).2
    have hc : (c : V) = a - B Q.y a • x := by
      rw [Q.split_symm_snd, hxQ, hax, zero_smul, sub_zero]
    have hgc : f (p c) = 0 := DFunLike.congr_fun h c
    rw [hc, map_sub, map_sub, map_smul, map_smul, hap, hfx, smul_zero, sub_zero] at hgc
    exact hgc
  obtain ⟨y, hyy, hy⟩ := T.exists_isotropic_map_ne_zero hC h2 g hgn
  refine ⟨x, y, hxx, ?_, hyy, hy⟩
  rw [← hxQ]
  exact ((Q.mem_orthogonalComplement y).mp y.property).1

end IsotropicProjection

end Langlands.SymmetricBilinear

namespace Langlands.GroupScheme.Quaternionic

open Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A]
  {I : Type} [Fintype I] [DecidableEq I]
  (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (τ : FirstKindInvolution R A)
  (hτ : ∀ a : A, e (τ a) * FirstKindInvolution.gramTwo R =
    FirstKindInvolution.gramTwo R * (e a)ᵀ)

include hτ in
/-- A nonsingular skew-hermitian row form of rank at least four over a split
quaternion algebra has an isotropic row with a unit at any chosen coordinate
when quadratic forms of dimension greater than four are isotropic. -/
theorem exists_isotropic_row_unit_of_splitSkew (h2 : (2 : R) ≠ 0)
    (his : ∀ (V : Type u) [AddCommGroup V] [Module R V] [FiniteDimensional R V]
      (Q : QuadraticForm R V), 4 < finrank R V → ∃ z, z ≠ 0 ∧ Q z = 0)
    (i : I) (hI : 4 ≤ Fintype.card I) {H : Matrix I I A}
    (hH : τ.matrix I H = -H) (hu : IsUnit H) :
    ∃ x : I → A, IsUnit (x i) ∧ τ.matrixSesqBilin H x x = 0 := by
  let M := splitSkewScalarGram e H
  let B := M.toBilin'
  have hs := Matrix.isSymm_toBilin'_iff_isSymm.mpr (splitSkewScalarGram_isSymm e τ hτ hH)
  have hB := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M
    (M.isUnit_iff_isUnit_det.mp (splitSkewScalarGram_isUnit e hu)).ne_zero
  have hdim : 8 ≤ finrank R (I × Fin 2 → R) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    omega
  let p : (I × Fin 2 → R) →ₗ[R] (Fin 2 → R) :=
    LinearMap.pi fun j => LinearMap.proj (i, j)
  have hp : Function.Surjective p := fun f => ⟨f ∘ Prod.snd, rfl⟩
  obtain ⟨a, b, haa, hab, hbb, hd⟩ :=
    exists_isotropic_pair_of_surjective_projection h2 hs hB hdim his p hp
  let X : Matrix (Fin 2) (I × Fin 2) R := Matrix.of ![a, b]
  let x := fromSplitSkewRows e X
  have hx : IsUnit (e (x i)) := by
    apply (e (x i)).isUnit_iff_isUnit_det.mpr
    rw [isUnit_iff_ne_zero, det_fin_two]
    simpa [x, fromSplitSkewRows, X, p] using hd
  let J := FirstKindInvolution.gramTwo R
  have hz : e (τ.matrixSesqBilin H x x) * J = 0 := by
    ext r s
    rw [← splitSkewScalarGram_pairing e τ hτ, show splitSkewRows e x = X from
      splitSkewRows_fromSplitSkewRows e X]
    change B (![a, b] r) (![a, b] s) = 0
    have hba := (hs.eq b a).trans hab
    fin_cases r <;> fin_cases s <;> assumption
  refine ⟨x, by simpa only [AlgEquiv.symm_apply_apply] using hx.map e.symm, e.injective ?_⟩
  rw [_root_.map_zero]
  exact (FirstKindInvolution.isUnit_gramTwo (D := R)).mul_left_inj.mp (by simpa only [zero_mul] using hz)

/-- The invertible-coordinate isotropy assertion for a split quaternion chart. -/
def SplitSkewNonsingularIsotropyStatement : Prop :=
  ∀ (R : Type u) (A : Type v) [Field R] [Ring A] [Algebra R A],
    (2 : R) ≠ 0 →
    (∀ (V : Type u) [AddCommGroup V] [Module R V] [FiniteDimensional R V]
      (Q : QuadraticForm R V), 4 < finrank R V → ∃ z, z ≠ 0 ∧ Q z = 0) →
    ∀ (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (τ : FirstKindInvolution R A),
    (∀ a : A, e (τ a) * FirstKindInvolution.gramTwo R =
      FirstKindInvolution.gramTwo R * (e a)ᵀ) →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I), 4 ≤ Fintype.card I →
    ∀ H : Matrix I I A, τ.matrix I H = -H → IsUnit H →
      ∃ x : I → A, IsUnit (x i) ∧ τ.matrixSesqBilin H x x = 0

theorem splitSkewNonsingularIsotropy : SplitSkewNonsingularIsotropyStatement.{u, v} := by
  intro R A _ _ _ h2 his e τ hτ I _ _ i hI H hH hu
  exact exists_isotropic_row_unit_of_splitSkew e τ hτ h2 his i hI hH hu

end Langlands.GroupScheme.Quaternionic
