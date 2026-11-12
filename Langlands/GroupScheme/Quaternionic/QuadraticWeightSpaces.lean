import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Singular weight spaces for a division-algebra quadratic form -/

noncomputable section

universe u v w s

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- The quotient-valued form is homogeneous of degree two under central scalars. -/
theorem quadraticValue_central_smul (c : K) (x : n → D) (q : σ.QuadraticForms n) :
    σ.quadraticValue (c • x) q = (c * c) • σ.quadraticValue x q := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    rw [quadraticValue_mk, quadraticValue_mk, sesqForm_smul_left_scalar,
      sesqForm_smul_right_scalar, smul_smul, Submodule.Quotient.mk_smul]

/-- The quadratic value on the sum of two singular lines scales by the product of scalars. -/
theorem quadraticValue_singular_pair_central_smul (q : σ.QuadraticForms n)
    (x y : n → D) (hx : σ.quadraticValue x q = 0) (hy : σ.quadraticValue y q = 0)
    (c c' : K) :
    σ.quadraticValue (c • x + c' • y) q = (c * c') • σ.quadraticValue (x + y) q := by
  rw [quadraticValue_add, quadraticValue_central_smul, quadraticValue_central_smul,
    hx, hy, smul_zero, smul_zero, zero_add, zero_add,
    sesqForm_smul_left_scalar, sesqForm_smul_right_scalar, smul_smul,
    Submodule.Quotient.mk_smul,
    quadraticValue_add, hx, hy, zero_add, zero_add]

variable {G : Type s} (ρ : G → Module.End D (n → D))

/-- The division-algebra subspace on which every operator has the specified central scalar. -/
def scalarWeightSpace (χ : G → K) : Submodule D (n → D) where
  carrier := {v | ∀ g, ρ g v = χ g • v}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro x y hx hy g
    rw [LinearMap.map_add, hx g, hy g, smul_add]
  smul_mem' := by
    intro a x hx g
    rw [LinearMap.map_smul, hx g, smul_comm]

variable {σ ρ}

omit [DecidableEq n] [Fintype n] in
/-- Distinct scalar weights have disjoint division-algebra weight spaces. -/
theorem disjoint_scalarWeightSpace {χ ψ : G → K} (h : χ ≠ ψ) :
    Disjoint (scalarWeightSpace ρ χ) (scalarWeightSpace ρ ψ) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  by_contra hv0
  apply h
  funext g
  exact smul_left_injective K hv0 ((hv g).symm.trans (hw g))

private theorem eq_zero_of_scalar_smul_eq_self {M : Type*} [AddCommGroup M] [Module K M]
    {c : K} {z : M} (hc : c ≠ 1) (hz : c • z = z) : z = 0 := by
  have he : (c - 1) • z = 0 := by rw [sub_smul, one_smul, hz, sub_self]
  exact (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hc)

/-- A nontrivial squared weight has a totally singular weight space under value-preserving operators. -/
theorem isTotallySingular_scalarWeightSpace (q : σ.QuadraticForms n)
    (hρ : ∀ g z, σ.quadraticValue (ρ g z) q = σ.quadraticValue z q)
    (χ : G → K) (hχ : ∃ g, χ g * χ g ≠ 1) :
    σ.IsTotallySingular q (scalarWeightSpace ρ χ) := by
  obtain ⟨g, hg⟩ := hχ
  intro v hv
  apply eq_zero_of_scalar_smul_eq_self hg
  rw [← quadraticValue_central_smul, ← hv g, hρ]

/-- Weight spaces whose individual squares and mutual product are nontrivial span a singular subspace. -/
theorem isTotallySingular_sup_scalarWeightSpace (q : σ.QuadraticForms n)
    (hρ : ∀ g z, σ.quadraticValue (ρ g z) q = σ.quadraticValue z q)
    (χ ψ : G → K) (hχ : ∃ g, χ g * χ g ≠ 1) (hψ : ∃ g, ψ g * ψ g ≠ 1)
    (hχψ : ∃ g, χ g * ψ g ≠ 1) :
    σ.IsTotallySingular q (scalarWeightSpace ρ χ ⊔ scalarWeightSpace ρ ψ) := by
  obtain ⟨g, hg⟩ := hχψ
  intro z hz
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
  have hvq := isTotallySingular_scalarWeightSpace q hρ χ hχ v hv
  have hwq := isTotallySingular_scalarWeightSpace q hρ ψ hψ w hw
  apply eq_zero_of_scalar_smul_eq_self hg
  rw [← quadraticValue_singular_pair_central_smul σ q v w hvq hwq,
    ← hv g, ← hw g, ← LinearMap.map_add, hρ]

/-- Two distinct nonzero such weight spaces force quadratic Witt index at least two. -/
theorem two_le_quadraticWittIndex_of_scalarWeightSpaces (q : σ.QuadraticForms n)
    (hρ : ∀ g z, σ.quadraticValue (ρ g z) q = σ.quadraticValue z q)
    (χ ψ : G → K) (hne : χ ≠ ψ)
    (hχ : ∃ g, χ g * χ g ≠ 1) (hψ : ∃ g, ψ g * ψ g ≠ 1)
    (hχψ : ∃ g, χ g * ψ g ≠ 1)
    (hWχ : scalarWeightSpace ρ χ ≠ ⊥) (hWψ : scalarWeightSpace ρ ψ ≠ ⊥) :
    2 ≤ σ.quadraticWittIndex q := by
  have hpos (θ : G → K) (hθ : scalarWeightSpace ρ θ ≠ ⊥) :
      0 < Module.finrank D (scalarWeightSpace ρ θ) := by
    obtain ⟨v, hv, hv0⟩ := (scalarWeightSpace ρ θ).ne_bot_iff.mp hθ
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, hv⟩, fun he => hv0 (congrArg Subtype.val he)⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (scalarWeightSpace ρ χ) (scalarWeightSpace ρ ψ)
  rw [(disjoint_scalarWeightSpace hne).eq_bot, finrank_bot, add_zero] at hdim
  have hbound := (isTotallySingular_sup_scalarWeightSpace q hρ χ ψ hχ hψ hχψ).finrank_le_quadraticWittIndex
  have hpχ := hpos χ hWχ
  have hpψ := hpos ψ hWψ
  omega

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
