import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCharDeriv

/-! # Expanding powers of an archimedean derivative over words

A power `(R_Z)^K` of the derivative along `Z` is a combination of composites of derivatives along
fixed matrix units, with coefficients bounded by `(M A)^K` when the entries of `Z` have norm at
most `A`. Consequently `‖W_{(R_Z)^K f}‖` is bounded by finitely many Whittaker functions that do
not depend on `Z`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance wordsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance wordsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Words

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
  (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V)
  {S : Type*} [Fintype S] (D : S → ArchimedeanMatrix F (r + 1))

/-- The composite `R(D_(l 0)) ∘ ⋯ ∘ R(D_(l (K-1)))` along a word `l`. -/
def wordOp : (K : ℕ) → (Fin K → S) → (V →ₗ[ℂ] V)
  | 0, _ => 1
  | K + 1, l => R (D (l 0)) * wordOp K (Fin.tail l)

/-- **Word expansion.** If every `Z` is `Σ_s c(Z)_s D_s`, then
`(R_Z)^K = Σ_l (Π_k c(Z)_(l k)) R(D_(l 0)) ∘ ⋯ ∘ R(D_(l (K-1)))`. -/
theorem pow_eq_sum_wordOp (c : ArchimedeanMatrix F (r + 1) → S → ℝ)
    (hc : ∀ Z, Z = ∑ s, c Z s • D s) (Z : ArchimedeanMatrix F (r + 1)) (K : ℕ) :
    R Z ^ K = ∑ l : Fin K → S, (∏ k, c Z (l k)) • wordOp F R D K l := by
  induction K with
  | zero =>
    simp only [pow_zero, Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_smul,
      Finset.sum_singleton]
    rfl
  | succ K ih =>
    have hR : R Z = ∑ s, c Z s • R (D s) := by
      conv_lhs => rw [hc Z]
      rw [map_sum]
      simp only [map_smul]
    rw [pow_succ', ih, hR, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Fin.consEquiv_apply]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, wordOp, smul_mul_smul_comm]
    rfl

end Words

section Entries

open scoped Classical

/-- The fixed real basis of the mixed space. -/
abbrev mixedBasis : Module.Basis (Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))) ℝ
    (mixedEmbedding.mixedSpace F) :=
  Module.finBasis ℝ (mixedEmbedding.mixedSpace F)

/-- Indices of the real matrix units: an entry position and a basis vector. -/
abbrev EntryIndex (n : ℕ) : Type :=
  Fin n × Fin n × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))

/-- The real matrix unit with entry `e_k` at `(a, b)`. -/
def entryUnit (n : ℕ) (s : EntryIndex F n) : ArchimedeanMatrix F n :=
  Matrix.single s.1 s.2.1 (mixedBasis F s.2.2)

/-- The coordinate of `Z` along the matrix unit `s`. -/
def entryCoord (n : ℕ) (Z : ArchimedeanMatrix F n) (s : EntryIndex F n) : ℝ :=
  (mixedBasis F).repr (Z s.1 s.2.1) s.2.2

theorem eq_sum_entryCoord (n : ℕ) (Z : ArchimedeanMatrix F n) :
    Z = ∑ s, entryCoord F n Z s • entryUnit F n s := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [Fintype.sum_prod_type, entryCoord, entryUnit]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [← (mixedBasis F).sum_repr (Z a b)]
  rw [← Matrix.singleLinearMap_apply ℝ a b, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Matrix.singleLinearMap_apply]

/-- A constant bounding all basis coordinates of the mixed space by the norm. -/
def coordConst : ℝ :=
  ∑ k, ‖LinearMap.toContinuousLinearMap ((mixedBasis F).coord k)‖

theorem coordConst_nonneg : 0 ≤ coordConst F :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem abs_entryCoord_le (n : ℕ) (Z : ArchimedeanMatrix F n) {A : ℝ}
    (hA : ∀ a b, ‖Z a b‖ ≤ A) (s : EntryIndex F n) :
    |entryCoord F n Z s| ≤ coordConst F * A := by
  have h1 : |entryCoord F n Z s| ≤
      ‖LinearMap.toContinuousLinearMap ((mixedBasis F).coord s.2.2)‖ * ‖Z s.1 s.2.1‖ := by
    have := (LinearMap.toContinuousLinearMap ((mixedBasis F).coord s.2.2)).le_opNorm
      (Z s.1 s.2.1)
    simpa [entryCoord, Real.norm_eq_abs] using this
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA s.1 s.2.1)
  refine h1.trans ?_
  have h2 : ‖LinearMap.toContinuousLinearMap ((mixedBasis F).coord s.2.2)‖ ≤ coordConst F :=
    Finset.single_le_sum (f := fun k =>
      ‖LinearMap.toContinuousLinearMap ((mixedBasis F).coord k)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  exact mul_le_mul h2 (hA _ _) (norm_nonneg _) (coordConst_nonneg F)

end Entries

section Bound

open scoped Classical

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
  {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V} (hV : WhittakerDecayClass F r V R)
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

include hV in
/-- A function of a decay class is bounded on `N(𝔸) g`. -/
theorem WhittakerDecayClass.exists_bound_unipotent (f : V) (g : Points F (r + 1)) :
    ∃ B : ℝ, ∀ u : unipotentAdelic F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) ((u : Points F (r + 1)) * g)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hV.bounded f (detNorm F (r + 1) g) (detNorm F (r + 1) g)
    (detNorm_pos F (r + 1) g)
  refine ⟨B, fun u => hB _ ?_ ?_⟩ <;> rw [detNorm_mul, detNorm_unipotent, one_mul]

/-- `f ↦ W_f(g)` as a complex-linear functional on a decay class. -/
def whittakerLinear (g : Points F (r + 1)) : V →ₗ[ℂ] ℂ where
  toFun f := whittaker F r ψ (f : Points F (r + 1) → ℂ) g
  map_add' f f' := by
    obtain ⟨B, hB⟩ := hV.exists_bound_unipotent F f g
    obtain ⟨B', hB'⟩ := hV.exists_bound_unipotent F f' g
    rw [Submodule.coe_add]
    exact whittaker_add F ψ hψ f f' (hV.continuous f) (hV.continuous f')
      (fun k hk x => hV.rational f k hk x) (fun k hk x => hV.rational f' k hk x) g B B' hB hB'
  map_smul' c f := by
    rw [Submodule.coe_smul]
    exact whittaker_smul F ψ c f g

theorem whittakerLinear_apply (g : Points F (r + 1)) (f : V) :
    whittakerLinear F hV ψ hψ g f = whittaker F r ψ (f : Points F (r + 1) → ℂ) g := rfl

/-- The word composite along the matrix units. -/
abbrev entryWord (K : ℕ) (l : Fin K → EntryIndex F (r + 1)) : V →ₗ[ℂ] V :=
  wordOp F R (entryUnit F (r + 1)) K l

include hV hψ in
/-- **Bound by finitely many words.** If the entries of `Z` have norm at most `A`, then
`‖W_{(R_Z)^K f}(g)‖ ≤ (M A)^K Σ_l ‖W_{f_l}(g)‖`, where `f_l` runs over the finitely many word
composites of length `K` applied to `f`, independent of `Z`. -/
theorem norm_whittaker_pow_le (Z : ArchimedeanMatrix F (r + 1)) {A : ℝ}
    (hA : ∀ a b, ‖Z a b‖ ≤ A) (K : ℕ) (f : V) (g : Points F (r + 1)) :
    ‖whittaker F r ψ (((R Z) ^ K) f : Points F (r + 1) → ℂ) g‖ ≤
      (coordConst F * A) ^ K *
        ∑ l : Fin K → EntryIndex F (r + 1),
          ‖whittaker F r ψ ((entryWord F (R := R) K l f : V) : Points F (r + 1) → ℂ) g‖ := by
  rw [← whittakerLinear_apply F hV ψ hψ,
    pow_eq_sum_wordOp F R (entryUnit F (r + 1)) (entryCoord F (r + 1))
      (eq_sum_entryCoord F (r + 1)) Z K,
    LinearMap.sum_apply, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
    Finset.abs_prod, whittakerLinear_apply]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun k => |entryCoord F (r + 1) Z (l k)|) (g := fun _ => coordConst F * A)
    (fun k _ => abs_nonneg _) (fun k _ => abs_entryCoord_le F (r + 1) Z hA (l k))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end Bound

end Langlands.Global.RankinSelbergGlobal.Unfolding
