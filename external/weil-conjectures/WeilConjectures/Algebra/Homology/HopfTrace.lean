/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.Mathlib.Algebra.BigOperators.Finprod
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.LinearAlgebra.Trace

/-!
# The Hopf trace formula

For a bounded cochain complex `P` of finite dimensional vector spaces over a field `K` and a
chain endomorphism `v` of `P`, the alternating sum of the traces of the components of `v` equals
the alternating sum of the traces of the maps it induces on homology:

`∑ i, (-1) ^ i * Tr (v ^ i ∣ P ^ i) = ∑ i, (-1) ^ i * Tr (H ^ i (v) ∣ H ^ i (P))`

(`CochainComplex.sum_negOnePow_smul_trace_f_eq_sum_negOnePow_smul_trace_homologyMap`).

The proof uses the additivity of the trace (`LinearMap.trace_eq_trace_add_trace_of_exact`) along
the short exact sequences `0 → Z ^ i → P ^ i → B ^ (i + 1) → 0` and
`0 → B ^ i → Z ^ i → H ^ i → 0`, which is the content of
`CategoryTheory.ShortComplex.trace_τ₂_eq_add_trace_homologyMap` for a short complex of vector
spaces; the contributions of the boundaries then cancel in the alternating sum.

This is the linear algebra behind blueprint `proposition-properties-trace`, item (4).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {K : Type*} [Field K] {S : ShortComplex (ModuleCat K)}

/-- The image of the first map of a short complex of modules is stable under an endomorphism of
the short complex. -/
lemma moduleCat_mapsTo_range_f (φ : S ⟶ S) :
    ∀ x ∈ LinearMap.range S.f.hom, φ.τ₂.hom x ∈ LinearMap.range S.f.hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨φ.τ₁.hom y, congr($(φ.comm₁₂).hom y)⟩

/-- The image of the second map of a short complex of modules is stable under an endomorphism
of the short complex. -/
lemma moduleCat_mapsTo_range_g (φ : S ⟶ S) :
    ∀ x ∈ LinearMap.range S.g.hom, φ.τ₃.hom x ∈ LinearMap.range S.g.hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨φ.τ₂.hom y, congr($(φ.comm₂₃).hom y)⟩

/-- The kernel of the second map of a short complex of modules is stable under an endomorphism
of the short complex. -/
lemma moduleCat_mapsTo_ker_g (φ : S ⟶ S) :
    ∀ x ∈ LinearMap.ker S.g.hom, φ.τ₂.hom x ∈ LinearMap.ker S.g.hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, φ.comm₂₃, ModuleCat.hom_comp,
    LinearMap.comp_apply, hx, map_zero]

/-- For an endomorphism `φ` of a short complex `S : X₁ ⟶ X₂ ⟶ X₃` of vector spaces with `X₂`
finite dimensional, the trace of `φ` on `X₂` is the sum of its traces on the image of `f`, on the
image of `g` and on the homology of `S`. -/
theorem trace_τ₂_eq_add_trace_homologyMap [FiniteDimensional K S.X₂] (φ : S ⟶ S) :
    LinearMap.trace K S.X₂ φ.τ₂.hom =
      LinearMap.trace K (LinearMap.range S.f.hom)
          (φ.τ₂.hom.restrict (moduleCat_mapsTo_range_f φ)) +
        LinearMap.trace K (LinearMap.range S.g.hom)
          (φ.τ₃.hom.restrict (moduleCat_mapsTo_range_g φ)) +
        LinearMap.trace K S.homology (homologyMap φ).hom := by
  have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
    rintro _ ⟨x, rfl⟩
    exact congr($(S.zero).hom x)
  -- `0 → Z → X₂ → B' → 0`, where `Z = ker g` and `B' = range g`
  have h₁ := LinearMap.trace_eq_trace_add_trace_of_exact
    (f := (LinearMap.ker S.g.hom).subtype) (g := S.g.hom.rangeRestrict)
    (fun x ↦ by simp [Subtype.ext_iff])
    (Submodule.injective_subtype _) S.g.hom.surjective_rangeRestrict
    (φM := φ.τ₂.hom.restrict (moduleCat_mapsTo_ker_g φ)) (φN := φ.τ₂.hom)
    (φP := φ.τ₃.hom.restrict (moduleCat_mapsTo_range_g φ)) (by ext; rfl)
    (by ext x; exact congr($(φ.comm₂₃).hom x))
  -- `0 → B → Z → H → 0`, where `B = range f`
  let π : LinearMap.ker S.g.hom →ₗ[K] S.homology :=
    (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom
  have hπ (z : LinearMap.ker S.g.hom) :
      π z = S.moduleCatHomologyIso.inv (Submodule.Quotient.mk z) :=
    S.moduleCatCyclesIso_inv_π_apply z
  have h₂ := LinearMap.trace_eq_trace_add_trace_of_exact
    (f := Submodule.inclusion hle) (g := π) ?_ (Submodule.inclusion_injective hle) ?_
    (φM := φ.τ₂.hom.restrict (moduleCat_mapsTo_range_f φ))
    (φN := φ.τ₂.hom.restrict (moduleCat_mapsTo_ker_g φ)) (φP := (homologyMap φ).hom)
    (by ext; rfl) ?_
  · rw [h₁, h₂, add_right_comm]
  · intro z
    have hinj : Function.Injective S.moduleCatHomologyIso.inv :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    rw [hπ, ← map_zero (ConcreteCategory.hom S.moduleCatHomologyIso.inv), hinj.eq_iff,
      Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨⟨S.f y, y, rfl⟩, Subtype.ext (congrArg Subtype.val hy)⟩
    · rintro ⟨⟨_, y, rfl⟩, hy⟩
      exact ⟨y, Subtype.ext (congrArg Subtype.val hy)⟩
  · exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  · ext z
    have hi : Function.Injective S.iCycles := (ModuleCat.mono_iff_injective _).1 inferInstance
    have hc : S.cyclesMap φ (S.moduleCatCyclesIso.inv z) =
        S.moduleCatCyclesIso.inv (φ.τ₂.hom.restrict (moduleCat_mapsTo_ker_g φ) z) := by
      apply hi
      simp only [← CategoryTheory.comp_apply, Category.assoc, cyclesMap_i,
        moduleCatCyclesIso_inv_iCycles_assoc, moduleCatCyclesIso_inv_iCycles]
      rfl
    refine (congrArg S.homologyπ hc).symm.trans ?_
    exact (ConcreteCategory.congr_hom (homologyπ_naturality φ) (S.moduleCatCyclesIso.inv z)).symm

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {K : Type*} [Field K] {ι : Type*} {c : ComplexShape ι}
  {P : HomologicalComplex (ModuleCat K) c}

/-- The image of a differential of a complex of modules is stable under a chain endomorphism. -/
lemma moduleCat_mapsTo_range_d (v : P ⟶ P) (i j : ι) :
    ∀ x ∈ LinearMap.range (P.d i j).hom, (v.f j).hom x ∈ LinearMap.range (P.d i j).hom := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(v.f i).hom y, congr($(v.comm i j).hom y)⟩

/-- For a chain endomorphism `v` of a complex `P` of vector spaces with `P j` finite
dimensional, the trace of `v` on `P j` is the sum of its traces on the boundaries `B j`, on the
image `B k` of the outgoing differential, and on the homology `H j`. -/
theorem trace_f_eq_add_trace_homologyMap (v : P ⟶ P) {i j k : ι} [FiniteDimensional K (P.X j)]
    (hi : c.prev j = i) (hk : c.next j = k) :
    LinearMap.trace K (P.X j) (v.f j).hom =
      LinearMap.trace K (LinearMap.range (P.d i j).hom)
          ((v.f j).hom.restrict (moduleCat_mapsTo_range_d v i j)) +
        LinearMap.trace K (LinearMap.range (P.d j k).hom)
          ((v.f k).hom.restrict (moduleCat_mapsTo_range_d v j k)) +
        LinearMap.trace K (P.homology j) (homologyMap v j).hom := by
  subst hi hk
  have : FiniteDimensional K (P.sc j).X₂ := ‹FiniteDimensional K (P.X j)›
  exact (P.sc j).trace_τ₂_eq_add_trace_homologyMap ((shortComplexFunctor _ _ j).map v)

end HomologicalComplex

namespace CochainComplex

open HomologicalComplex

variable {K : Type*} [Field K]

/-- The trace of a chain endomorphism on the image of a differential leaving a zero term
vanishes. -/
lemma trace_restrict_range_d_eq_zero_of_isZero {P : CochainComplex (ModuleCat K) ℤ}
    (v : P ⟶ P) {i j : ℤ} (h : IsZero (P.X i) ∨ IsZero (P.X j)) :
    LinearMap.trace K (LinearMap.range (P.d i j).hom)
      ((v.f j).hom.restrict (moduleCat_mapsTo_range_d v i j)) = 0 := by
  have : Subsingleton (LinearMap.range (P.d i j).hom) := by
    rcases h with h | h
    · have := ModuleCat.subsingleton_of_isZero h
      refine ⟨?_⟩
      rintro ⟨_, y, rfl⟩ ⟨_, y', rfl⟩
      rw [Subsingleton.elim y y']
    · have := ModuleCat.subsingleton_of_isZero h
      infer_instance
  exact LinearMap.trace_eq_zero_of_subsingleton _

/-- **The Hopf trace formula** (blueprint `proposition-properties-trace`, item (4), linear algebra
part): for a bounded cochain complex `P` of finite dimensional vector spaces over a field `K` and
a chain endomorphism `v` of `P`,

`∑ i, (-1) ^ i * Tr (v ^ i ∣ P ^ i) = ∑ i, (-1) ^ i * Tr (H ^ i (v) ∣ H ^ i (P))`. -/
theorem sum_negOnePow_smul_trace_f_eq_sum_negOnePow_smul_trace_homologyMap
    (P : CochainComplex (ModuleCat K) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i)) (hfin : ∀ i, Module.Finite K (P.X i)) :
    ∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace K (P.X i) (v.f i).hom =
      ∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace K (P.homology i) (homologyMap v i).hom := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ → K, ∀ a, B a = LinearMap.trace K (LinearMap.range (P.d a (a + 1)).hom)
      ((v.f (a + 1)).hom.restrict (moduleCat_mapsTo_range_d v a (a + 1))) := ⟨_, fun _ ↦ rfl⟩
  have key (a : ℤ) : LinearMap.trace K (P.X (a + 1)) (v.f (a + 1)).hom =
      B a + B (a + 1) + LinearMap.trace K (P.homology (a + 1)) (homologyMap v (a + 1)).hom := by
    rw [hB, hB]
    exact trace_f_eq_add_trace_homologyMap v (by simp) (by simp)
  have key' (i : ℤ) : LinearMap.trace K (P.X i) (v.f i).hom =
      B (i - 1) + B i + LinearMap.trace K (P.homology i) (homologyMap v i).hom := by
    have := key (i - 1)
    rwa [sub_add_cancel] at this
  have hc := Finset.sum_comp_add_one_eq_sum s (fun i ↦ (i.negOnePow : ℤ) • B (i - 1))
    (fun i hi ↦ by
      rw [hB, sub_add_cancel, trace_restrict_range_d_eq_zero_of_isZero v (.inr (hs i hi)),
        smul_zero])
    (fun i hi ↦ by
      rw [add_sub_cancel_right, hB, trace_restrict_range_d_eq_zero_of_isZero v (.inl (hs i hi)),
        smul_zero])
  simp only [Int.negOnePow_succ, add_sub_cancel_right, Units.val_neg, neg_smul] at hc
  simp only [key', smul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hc ⊢
  rw [← hc, neg_add_cancel, zero_add]

end CochainComplex
