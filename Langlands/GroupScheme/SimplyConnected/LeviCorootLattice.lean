import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! # Integral saturation for the coroot lattice of a Levi subgroup -/

noncomputable section

open Function Set Submodule

namespace Langlands.LinearAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- An integral submodule is saturated if every element whose nonzero integer
multiple belongs to it already belongs to it. -/
def IsSaturatedIntSubmodule (p : Submodule ℤ X) : Prop :=
  ∀ (n : ℤ), n ≠ 0 → ∀ x : X, n • x ∈ p → x ∈ p

/-- The span of a subset of an integral basis is saturated. -/
theorem mem_span_basis_of_zsmul_mem (b : Module.Basis ι ℤ X) (s : Set ι)
    {n : ℤ} (hn : n ≠ 0) {x : X}
    (hx : n • x ∈ span ℤ (b '' s)) : x ∈ span ℤ (b '' s) := by
  rw [b.mem_span_image] at hx ⊢
  intro i hi
  apply hx
  simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hi ⊢
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_ne_zero hn hi

/-- Every span of a subset of an integral basis is saturated. -/
theorem isSaturatedIntSubmodule_span_basis (b : Module.Basis ι ℤ X) (s : Set ι) :
    IsSaturatedIntSubmodule (span ℤ (b '' s)) :=
  fun _ hn _ hx => mem_span_basis_of_zsmul_mem b s hn hx

/-- A base whose coroots span the entire integral lattice gives saturated spans
for all subsets of its simple coroots. -/
theorem mem_span_simple_coroots_of_zsmul_mem
    {P : RootPairing ι ℤ X Y} (b : P.Base) (hP : P.corootSpan ℤ = ⊤)
    (s : Set ι) (hs : s ⊆ (b.support : Set ι)) {n : ℤ} (hn : n ≠ 0) {y : Y}
    (hy : n • y ∈ span ℤ (P.coroot '' s)) :
    y ∈ span ℤ (P.coroot '' s) := by
  let v : b.support → Y := fun i => P.coroot i
  have hspan : ⊤ ≤ span ℤ (range v) := by
    have hv : range v = P.coroot '' (b.support : Set ι) := by
      ext y
      simp [v]
    rw [hv, b.span_coroot_support, hP]
  let e : Module.Basis b.support ℤ Y := Module.Basis.mk b.linearIndepOn_coroot hspan
  have he : e '' {i : b.support | (i : ι) ∈ s} = P.coroot '' s := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by simp [e]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hs hi⟩, hi, by simp [e]⟩
  rw [← he] at hy ⊢
  exact mem_span_basis_of_zsmul_mem e _ hn hy

/-- Every subset of a spanning system of simple coroots has saturated span. -/
theorem isSaturatedIntSubmodule_span_simple_coroots
    {P : RootPairing ι ℤ X Y} (b : P.Base) (hP : P.corootSpan ℤ = ⊤)
    (s : Set ι) (hs : s ⊆ (b.support : Set ι)) :
    IsSaturatedIntSubmodule (span ℤ (P.coroot '' s)) :=
  fun _ hn _ hy => mem_span_simple_coroots_of_zsmul_mem b hP s hs hn hy

/-- An injectively mapped finite-index submodule with saturated image is the
entire source module. -/
theorem eq_top_of_finite_quotient_map_saturated (p : Submodule ℤ Y)
    [Finite (Y ⧸ p)] (f : Y →ₗ[ℤ] X) (hf : Injective f)
    (hsat : IsSaturatedIntSubmodule (p.map f)) : p = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  have hfin : IsOfFinAddOrder (Submodule.Quotient.mk (p := p) y) :=
    isOfFinAddOrder_of_finite _
  let n : ℕ := addOrderOf (Submodule.Quotient.mk (p := p) y)
  have hn : 0 < n := hfin.addOrderOf_pos
  have hny : n • y ∈ p := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact addOrderOf_nsmul_eq_zero _
  have hnfy : (n : ℤ) • f y ∈ p.map f := ⟨n • y, hny, by simp⟩
  have hfy := hsat _ (Int.natCast_ne_zero.mpr hn.ne') _ hnfy
  obtain ⟨z, hz, hzy⟩ := hfy
  rwa [hf hzy] at hz

/-- An injectively mapped finite-index lattice must be the entire source lattice
if its image is spanned by a subset of an integral basis. -/
theorem eq_top_of_finite_quotient_map_eq_span_basis
    (b : Module.Basis ι ℤ X) (s : Set ι) (p : Submodule ℤ Y)
    [Finite (Y ⧸ p)] (f : Y →ₗ[ℤ] X) (hf : Injective f)
    (hmap : p.map f = span ℤ (b '' s)) : p = ⊤ := by
  apply eq_top_of_finite_quotient_map_saturated p f hf
  rw [hmap]
  exact isSaturatedIntSubmodule_span_basis b s

/-- Coroot-span comparison with a subset of simple coroots forces the smaller
coroots to span whenever the larger coroots do and the smaller span has finite index. -/
theorem corootSpan_eq_top_of_map_eq_span_simple_coroots
    {κ X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {P : RootPairing ι ℤ X Y} (b : P.Base) (hP : P.corootSpan ℤ = ⊤)
    (s : Set ι) (hs : s ⊆ (b.support : Set ι))
    (Q : RootPairing κ ℤ X' Y') [Finite (Y' ⧸ Q.corootSpan ℤ)]
    (f : Y' →ₗ[ℤ] Y) (hf : Injective f)
    (hmap : (Q.corootSpan ℤ).map f = span ℤ (P.coroot '' s)) :
    Q.corootSpan ℤ = ⊤ := by
  apply eq_top_of_finite_quotient_map_saturated (Q.corootSpan ℤ) f hf
  rw [hmap]
  exact isSaturatedIntSubmodule_span_simple_coroots b hP s hs

end Langlands.LinearAlgebra
