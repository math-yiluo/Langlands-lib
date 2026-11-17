import Langlands.GroupScheme.Quaternionic.HyperbolicPair
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.GroupScheme.Quaternionic.WittIndexOneInputs
import Langlands.GroupScheme.Quaternionic.LocalWittIndexOneDimension

/-! # Quadratic forms with zero quadratic radical -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open scoped Matrix

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The quadratic radical is zero: a singular vector orthogonal to every
vector is zero. This permits a nonzero polar radical in characteristic two. -/
def IsRadicalFreeQuadratic (q : σ.QuadraticForms n) : Prop :=
  ∀ x : n → D, σ.quadraticValue x q = 0 →
    (∀ y : n → D, σ.sesqForm (σ.polar q) x y = 0) → x = 0

/-- An invertible polar matrix implies that the quadratic radical is zero. -/
theorem IsNondegenerateQuadratic.isRadicalFree {q : σ.QuadraticForms n}
    (hq : σ.IsNondegenerateQuadratic q) : σ.IsRadicalFreeQuadratic q := by
  intro x _ hx
  by_contra hx0
  obtain ⟨y, hy⟩ := σ.exists_polar_partner q hq x hx0
  exact one_ne_zero (hy.symm.trans (hx y))

/-- For a form with zero quadratic radical, every nonzero singular vector
has a polar partner, even if the polar matrix is not invertible. -/
theorem exists_polar_partner_of_radicalFree (q : σ.QuadraticForms n)
    (hq : σ.IsRadicalFreeQuadratic q) (x : n → D) (hx : x ≠ 0)
    (hqx : σ.quadraticValue x q = 0) :
    ∃ y : n → D, σ.sesqForm (σ.polar q) x y = 1 := by
  classical
  have hxH : x ᵥ* σ.polar q ≠ 0 := by
    intro h
    apply hx
    apply hq x hqx
    intro y
    have hs : σ.sesqForm (σ.polar q) x y =
        ∑ j, (x ᵥ* σ.polar q) j * σ (y j) := by
      simp only [sesqForm, Matrix.vecMul_apply_eq_sum, Finset.sum_mul]
      exact Finset.sum_comm
    rw [hs, h]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  obtain ⟨j, hj⟩ : ∃ j, (x ᵥ* σ.polar q) j ≠ 0 := by
    by_contra! h
    exact hxH (funext h)
  refine ⟨Pi.single j (σ ((x ᵥ* σ.polar q) j)⁻¹), ?_⟩
  rw [sesqForm_single_right, apply_apply, mul_inv_cancel₀ hj]

/-- A singular vector outside zero extends to a hyperbolic pair under the
quadratic-radical condition, with no restriction on the characteristic. -/
theorem exists_hyperbolic_partner_of_radicalFree (q : σ.QuadraticForms n)
    (hq : σ.IsRadicalFreeQuadratic q) (x : n → D) (hx : x ≠ 0)
    (hqx : σ.quadraticValue x q = 0) :
    ∃ y : n → D, σ.IsHyperbolicPair q x y := by
  obtain ⟨y, hxy⟩ := σ.exists_polar_partner_of_radicalFree q hq x hx hqx
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_surjective σ.alternatingSubspace)
    (σ.quadraticValue y q)
  have hyx : σ.sesqForm (σ.polar q) y x = 1 := by
    rw [← sesqForm_polar_swap, hxy, map_one]
  have hxx : σ.sesqForm (σ.polar q) x x = 0 :=
    σ.sesqForm_polar_self_eq_zero q x hqx
  refine ⟨y + (-a) • x, hqx, ?_, ?_⟩
  · rw [quadraticValue_add, quadraticValue_smul_eq_zero σ (-a) x q hqx,
      sesqForm_smul_right, hyx, one_mul, map_neg, add_zero, ← ha]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, ← LinearMap.map_add]
    simpa only [Submodule.mkQ_apply, sub_eq_add_neg] using
      (Submodule.Quotient.mk_eq_zero σ.alternatingSubspace).mpr
        (σ.sub_mem_alternatingSubspace a)
  · rw [sesqForm_add_right, sesqForm_smul_right, hxx, zero_mul, add_zero, hxy]

/-- Positive Witt index and zero quadratic radical supply a hyperbolic pair. -/
theorem exists_hyperbolicPair_of_radicalFree_of_quadraticWittIndex_pos
    (q : σ.QuadraticForms n) (hq : σ.IsRadicalFreeQuadratic q)
    (hw : 0 < σ.quadraticWittIndex q) :
    ∃ x y : n → D, σ.IsHyperbolicPair q x y := by
  obtain ⟨x, hx, hqx⟩ := σ.exists_nonzero_singular_of_quadraticWittIndex_pos q hw
  obtain ⟨y, hy⟩ := σ.exists_hyperbolic_partner_of_radicalFree q hq x hx hqx
  exact ⟨x, y, hy⟩

section LocalScalar

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- An ordinary quadratic form over a nonarchimedean local field, with zero
quadratic radical and Witt index one, has dimension at most six. Its polar
matrix is allowed to be singular, including in odd dimension in characteristic
two. -/
theorem scalar_card_le_six_of_radicalFree_of_quadraticWittIndex_one
    {q : (scalar K).QuadraticForms n}
    (hq : (scalar K).IsRadicalFreeQuadratic q)
    (hw : (scalar K).quadraticWittIndex q = 1) :
    Fintype.card n ≤ 6 := by
  let σ := scalar K
  have hw' : σ.quadraticWittIndex q = 1 := hw
  obtain ⟨e, f, hP⟩ :=
    σ.exists_hyperbolicPair_of_radicalFree_of_quadraticWittIndex_pos q hq (by omega)
  have hP' : Eichler.IsHyperbolic σ q e f := ⟨hP.1, hP.2.1, hP.2.2⟩
  let φ := Eichler.pairFunctional σ q e f
  let W := LinearMap.ker φ
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective (σ.quadraticKernel n) q
  let QK : QuadraticForm K (n → K) :=
    LinearMap.BilinMap.toQuadraticMap (σ.sesqFormBilinear Q)
  let QW : QuadraticForm K W := QK.comp W.subtype
  have hQW : QW.Anisotropic := by
    intro x hx
    apply Subtype.ext
    have hx0 : σ.sesqForm Q x.val x.val = 0 := hx
    have hxq : σ.quadraticValue x.val (Submodule.Quotient.mk Q) = 0 := by
      rw [quadraticValue_mk, hx0, Submodule.Quotient.mk_zero]
    have hxφ : φ x.val = 0 := x.property
    exact Eichler.eq_zero_of_ortho_of_quadraticWittIndex_le_one hP' hw.le
      (congrArg Prod.fst hxφ) (congrArg Prod.snd hxφ) hxq
  have hK : Module.finrank K W ≤ 4 :=
    Langlands.localQuadraticAnisotropicDimensionBound K W QW hQW
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank K (LinearMap.range φ) ≤ 2 := by
    simpa using Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  change Module.finrank K (LinearMap.ker φ) ≤ 4 at hK
  omega

/-- In dimension at least seven, an ordinary quadratic form with zero
quadratic radical over a local field cannot have Witt index one. -/
theorem scalar_quadraticWittIndex_ne_one_of_seven_le
    {q : (scalar K).QuadraticForms n}
    (hq : (scalar K).IsRadicalFreeQuadratic q) (hn : 7 ≤ Fintype.card n) :
    (scalar K).quadraticWittIndex q ≠ 1 := by
  intro hw
  have := scalar_card_le_six_of_radicalFree_of_quadraticWittIndex_one hq hw
  omega

end LocalScalar

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
