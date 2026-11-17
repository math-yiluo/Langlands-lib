import Langlands.GroupScheme.Quaternionic.RadicalFreeQuadratic
import Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicFamily

/-! # Hyperbolic families for forms with zero quadratic radical -/

noncomputable section

universe u v

open scoped Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {σ : FirstKindInvolution K D} {n : Type} [Fintype n] [DecidableEq n]

/-- On a totally singular subspace of a quadratic-radical-free form, the polar
pairing has a dual family for every linearly independent family. -/
theorem exists_polar_dual_family_of_radicalFree (q : σ.QuadraticForms n)
    (hq : σ.IsRadicalFreeQuadratic q) (W : Submodule D (n → D))
    (hW : σ.IsTotallySingular q W)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → n → D) (hxW : ∀ k, x k ∈ W) (hx : LinearIndependent D x) :
    ∃ z : ι → n → D, ∀ k l, σ.sesqForm (σ.polar q) (x k) (z l) = if k = l then 1 else 0 := by
  let Ψ : (n → D) →ₗ[D] (ι → D) := LinearMap.pi (fun k => σ.polarFunctional q (x k))
  have hΨ : ∀ z k, Ψ z k = σ.sesqForm (σ.polar q) z (x k) := fun z k => rfl
  have hsurj : LinearMap.range Ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : ι → D := fun k => f fun j => if k = j then 1 else 0
    have hfv : ∀ v : ι → D, f v = ∑ k, v k * c k := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      rfl
    have hzero : ∀ z, ∑ k, σ.sesqForm (σ.polar q) z (x k) * c k = 0 := by
      intro z
      have h1 := hf (LinearMap.mem_range_self Ψ z)
      rw [LinearMap.mem_ker, hfv] at h1
      exact h1
    let v : n → D := ∑ k, σ (c k) • x k
    have hv : ∀ z, σ.sesqForm (σ.polar q) v z = 0 := by
      intro z
      apply σ.injective
      rw [sesqForm_polar_swap, sesqForm_sum_smul_right, map_zero]
      simp only [apply_apply]
      exact hzero z
    have hv0 : v = 0 :=
      hq v (hW v (W.sum_mem fun k _ => W.smul_mem _ (hxW k))) hv
    have hc : ∀ k, c k = 0 := by
      intro k
      have h1 := (Fintype.linearIndependent_iff.mp hx) (fun k => σ (c k)) hv0 k
      rw [← σ.apply_apply (c k), h1, map_zero]
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfv]
    simp [hc]
  have hex : ∀ l, ∃ z, Ψ z = Pi.single l 1 := by
    intro l
    have h1 : Pi.single l (1 : D) ∈ LinearMap.range Ψ := hsurj ▸ Submodule.mem_top
    exact h1
  choose z hz using hex
  refine ⟨z, fun k l => ?_⟩
  have h1 := congrFun (hz l) k
  rw [hΨ, Pi.single_apply] at h1
  rw [← sesqForm_polar_swap, h1]
  split_ifs <;> simp

/-- A form with zero quadratic radical admits a hyperbolic family whose length
is its quadratic Witt index, even when the polar form has a nonzero radical. -/
theorem exists_isHyperbolicFamily_of_radicalFree (q : σ.QuadraticForms n)
    (hq : σ.IsRadicalFreeQuadratic q) :
    ∃ x y : Fin (σ.quadraticWittIndex q) → n → D, σ.IsHyperbolicFamily q x y := by
  obtain ⟨W, hW, hdim⟩ := σ.exists_maximal_totallySingular q
  set r := σ.quadraticWittIndex q
  let bW : Module.Basis (Fin r) D W := Module.finBasisOfFinrankEq D W hdim
  let x : Fin r → n → D := fun k => (bW k : n → D)
  have hxW : ∀ k, x k ∈ W := fun k => (bW k).2
  have hx : LinearIndependent D x := bW.linearIndependent.map' W.subtype W.ker_subtype
  have hxx : ∀ k l, σ.sesqForm (σ.polar q) (x k) (x l) = 0 := fun k l =>
    hW.sesqForm_polar_eq_zero (hxW k) (hxW l)
  obtain ⟨z, hz⟩ := exists_polar_dual_family_of_radicalFree q hq W hW x hxW hx
  have hzx : ∀ k p, σ.sesqForm (σ.polar q) (z k) (x p) = if p = k then 1 else 0 := by
    intro k p
    rw [← sesqForm_polar_swap, hz p k]
    split_ifs <;> simp
  let s : Fin r → D := fun l => Quotient.out (σ.quadraticValue (z l) q)
  have hs : ∀ l, (Submodule.Quotient.mk (s l) : D ⧸ σ.alternatingSubspace) =
      σ.quadraticValue (z l) q := fun l => Submodule.Quotient.mk_out _
  let c : Fin r → Fin r → D := fun l k =>
    if l < k then -σ.sesqForm (σ.polar q) (z l) (z k) else if l = k then -σ (s l) else 0
  let y : Fin r → n → D := fun l => z l + ∑ k, c l k • x k
  have hsumW : ∀ l, ∑ k, c l k • x k ∈ W := fun l =>
    W.sum_mem fun k _ => W.smul_mem _ (hxW k)
  have hxy : ∀ k l, σ.sesqForm (σ.polar q) (x k) (y l) = if k = l then 1 else 0 := by
    intro k l
    simp only [y]
    rw [sesqForm_add_right, sesqForm_sum_smul_right, hz]
    simp [hxx]
  have hyy : ∀ k l, σ.sesqForm (σ.polar q) (y k) (y l) =
      σ.sesqForm (σ.polar q) (z k) (z l) + σ (c l k) + c k l := by
    intro k l
    rw [show y k = z k + ∑ m, c k m • x m from rfl, sesqForm_add_left, sesqForm_sum_smul_left]
    simp only [hxy]
    rw [show y l = z l + ∑ m, c l m • x m from rfl, sesqForm_add_right, sesqForm_sum_smul_right]
    simp only [hzx, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hqy : ∀ l, σ.quadraticValue (y l) q = 0 := by
    intro l
    simp only [y]
    rw [quadraticValue_add, hW _ (hsumW l), ← hs l, sesqForm_sum_smul_right]
    simp only [hzx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simp only [c, lt_irrefl, ite_false, ite_true, map_neg, apply_apply]
    rw [add_zero, ← Submodule.Quotient.mk_add, add_neg_cancel, Submodule.Quotient.mk_zero]
  refine ⟨x, y, ⟨fun k => hW _ (hxW k), hqy, hxy, hxx, fun k l => ?_⟩⟩
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [hyy]
    simp only [c, hkl, ite_true, not_lt.mpr hkl.le, hkl.ne', ite_false, map_zero, add_zero]
    exact add_neg_cancel _
  · exact σ.sesqForm_polar_self_eq_zero q _ (hqy k)
  · rw [hyy]
    simp only [c, hkl, ite_true, not_lt.mpr hkl.le, hkl.ne', ite_false, map_neg, add_zero,
      sesqForm_polar_swap]
    exact add_neg_cancel _

/-- A chosen hyperbolic family of maximal length for a quadratic-radical-free form. -/
def radicalFreeHyperbolicFamily (q : σ.QuadraticForms n)
    (hq : σ.IsRadicalFreeQuadratic q) :
    { p : (Fin (σ.quadraticWittIndex q) → n → D) ×
        (Fin (σ.quadraticWittIndex q) → n → D) // σ.IsHyperbolicFamily q p.1 p.2 } :=
  Classical.choice (by
    obtain ⟨x, y, hxy⟩ := exists_isHyperbolicFamily_of_radicalFree q hq
    exact ⟨⟨(x, y), hxy⟩⟩)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
