/-
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Adapted from the Anthropic Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, file
`P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean`
(its sections `Rep` and `Trace`).
Changes: declarations moved into `Langlands.FiniteRep.WeightSpaces`; groups and carriers may lie in
any universes; Mathlib is imported by module and no option is set; unused instance arguments are
omitted; linter clean-ups. The paired Markdown file lists the changes.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic

/-!
# Weight spaces of a commuting normal subgroup, and traces of permuted summands

Let `σ : Representation ℂ K W` be a representation of a finite group on a finite-dimensional
complex space, and `A` a subgroup whose image commutes. Every `σ a` is semisimple
(`isSemisimple`), so `W` is the internal direct sum of the common eigenspaces (weight spaces)
`wt σ A χ`, `χ : A → ℂ` (`isInternal_wt`); finitely many are nonzero (`finite_wt`), and a weight
with nonzero space is a character of `A` (`weightHom`). When `A` is normal, `K` acts on weights by
conjugation (the scoped instance `weightAction`), `σ k` maps `wt σ A χ` onto `wt σ A (k • χ)`
(`map_wt_eq`, `wtEquiv`), and the stabilizer of `χ` acts on `wt σ A χ` (`stabRep`).
`trace_eq_sum_fixed` computes the trace of a map that permutes the summands of an internal direct
sum: only the summands it fixes contribute.

This is the representation theory behind the monomial case of Brauer's theorem (`MonomialTrace`),
in the form of Serre's Propositions 19 and 24 (*Linear Representations of Finite Groups*, §7.1 and
§8.1) for traces of arbitrary, not necessarily irreducible, representations.
-/

noncomputable section

open scoped Classical
open Module

namespace Langlands.FiniteRep.WeightSpaces

universe u v

section Rep

variable {K : Type u} [Group K] [Fintype K]
variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (σ : Representation ℂ K W)

omit [FiniteDimensional ℂ W] in
/-- Every `σ k` is semisimple: it is annihilated by the separable polynomial `X ^ |K| - 1`. -/
theorem isSemisimple (k : K) : Module.End.IsSemisimple (σ k) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ Fintype.card K - Polynomial.C 1)
  · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast Fintype.card_ne_zero)
      one_ne_zero).squarefree
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, ← map_pow,
      pow_card_eq_one, map_one, sub_self]

omit [FiniteDimensional ℂ W] in
theorem maxGenEigenspace_eq (k : K) (μ : ℂ) :
    Module.End.maxGenEigenspace (σ k) μ = Module.End.eigenspace (σ k) μ :=
  (isSemisimple σ k).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

/-- `σ k` as a linear automorphism of `W`. -/
def act (k : K) : W ≃ₗ[ℂ] W :=
  { σ k with
    invFun := σ k⁻¹
    left_inv := fun v => by
      change (σ k⁻¹ * σ k) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    right_inv := fun v => by
      change (σ k * σ k⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl }

omit [Fintype K] [FiniteDimensional ℂ W] in
@[scoped simp] theorem act_apply (k : K) (v : W) : act σ k v = σ k v := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
theorem act_symm_apply (k : K) (v : W) : (act σ k).symm v = σ k⁻¹ v := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
theorem trace_conj (x g : K) :
    LinearMap.trace ℂ W (σ (x⁻¹ * g * x)) = LinearMap.trace ℂ W (σ g) := by
  rw [σ.map_mul, σ.map_mul, LinearMap.trace_mul_cycle, ← σ.map_mul, ← σ.map_mul, mul_inv_cancel,
    one_mul]

variable (A : Subgroup K)

/-- The weight space of `χ : A → ℂ`: the common generalized eigenspace of the `σ a` for the
eigenvalues `χ a` (an eigenspace, by `maxGenEigenspace_eq`). -/
def wt (χ : A → ℂ) : Submodule ℂ W := ⨅ a : A, Module.End.maxGenEigenspace (σ a) (χ a)

omit [FiniteDimensional ℂ W] in
theorem mem_wt (χ : A → ℂ) (v : W) : v ∈ wt σ A χ ↔ ∀ a : A, σ a v = χ a • v := by
  simp only [wt, Submodule.mem_iInf, maxGenEigenspace_eq, Module.End.mem_eigenspace_iff]

variable (hcomm : ∀ a b : A, σ a * σ b = σ b * σ a)
include hcomm

/-- If the image of `A` commutes, `W` is the internal direct sum of the weight spaces. -/
theorem isInternal_wt : DirectSum.IsInternal (wt σ A) := by
  have h1 : Pairwise fun a b : A => Commute (σ a) (σ b) := fun a b _ => hcomm a b
  have htop :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a : A => (σ a : Module.End ℂ W)) h1
    (fun a => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a : A => (σ a : Module.End ℂ W))
    (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) φ)
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop

omit hcomm [FiniteDimensional ℂ W] in
theorem mapsTo_wt_of_comm (χ : A → ℂ) (f : W →ₗ[ℂ] W) (hf : ∀ a : A, f * σ a = σ a * f) :
    Set.MapsTo f (wt σ A χ) (wt σ A χ) := by
  intro v hv
  rw [SetLike.mem_coe, mem_wt] at hv ⊢
  intro a
  have := congrArg (fun T => T v) (hf a)
  simp only [Module.End.mul_apply] at this
  rw [← this, hv a, map_smul]

omit hcomm in
theorem finite_wt (h : DirectSum.IsInternal (wt σ A)) : {χ : A → ℂ | wt σ A χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h.submodule_iSupIndep

omit hcomm

omit [Fintype K] [FiniteDimensional ℂ W] in
theorem exists_ne_zero_of_ne_bot {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) :
    ∃ v ∈ wt σ A χ, v ≠ 0 := by
  by_contra h
  push Not at h
  exact hχ ((Submodule.eq_bot_iff _).2 h)

omit [FiniteDimensional ℂ W] in
theorem weight_mul {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a b : A) : χ (a * b) = χ a * χ b := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_ne_bot σ A hχ
  rw [mem_wt] at hv
  have h1 : σ (a * b : A) v = χ (a * b) • v := hv (a * b)
  have h2 : σ (a * b : A) v = (χ a * χ b) • v := by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hv b, map_smul, hv a, smul_smul, mul_comm]
  have := h1.symm.trans h2
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at this
  rcases this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hv0

omit [FiniteDimensional ℂ W] in
theorem weight_one {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_ne_bot σ A hχ
  rw [mem_wt] at hv
  have h1 : σ (1 : A) v = χ 1 • v := hv 1
  rw [Subgroup.coe_one, map_one, Module.End.one_apply] at h1
  have : (χ 1 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact (sub_eq_zero.1 h)
  · exact absurd h hv0

omit [FiniteDimensional ℂ W] in
theorem weight_ne_zero {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a : A) : χ a ≠ 0 := by
  intro h
  have := weight_mul σ A hχ a⁻¹ a
  rw [inv_mul_cancel, weight_one σ A hχ, h, mul_zero] at this
  exact one_ne_zero this

/-- A weight with a nonzero weight space, as a character `A →* ℂˣ`. -/
def weightHom {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) : A →* ℂˣ where
  toFun a := Units.mk0 (χ a) (weight_ne_zero σ A hχ a)
  map_one' := Units.ext (weight_one σ A hχ)
  map_mul' a b := Units.ext (weight_mul σ A hχ a b)

omit [FiniteDimensional ℂ W] in
@[scoped simp] theorem weightHom_apply {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a : A) :
    ((weightHom σ A hχ a : ℂˣ) : ℂ) = χ a := rfl

variable [hA : A.Normal]

/-- For a normal subgroup `A`, the action of `K` on functions `A → ℂ` by conjugation:
`(k • χ) a = χ (k⁻¹ * a * k)`. -/
scoped instance weightAction : MulAction K (A → ℂ) where
  smul k χ := fun a => χ ⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩
  one_smul χ := by
    funext a
    change χ ⟨1⁻¹ * a * 1, _⟩ = χ a
    congr 1
    apply Subtype.ext
    simp
  mul_smul k₁ k₂ χ := by
    funext a
    change χ ⟨(k₁ * k₂)⁻¹ * a * (k₁ * k₂), _⟩ = χ ⟨k₂⁻¹ * (k₁⁻¹ * a * k₁ : K) * k₂, _⟩
    congr 1
    apply Subtype.ext
    simp only [mul_inv_rev]
    group

omit [Fintype K] in
theorem smul_weight_apply (k : K) (χ : A → ℂ) (a : A) :
    (k • χ) a = χ ⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩ := rfl

omit [FiniteDimensional ℂ W] in
theorem mapsTo_smul (k : K) (χ : A → ℂ) :
    Set.MapsTo (σ k) (wt σ A χ) (wt σ A (k • χ)) := by
  intro v hv
  rw [SetLike.mem_coe, mem_wt] at hv ⊢
  intro a
  rw [smul_weight_apply]
  have e : (a : K) = k * (k⁻¹ * a * k) * k⁻¹ := by group
  have : σ a (σ k v) = σ k (σ (⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩ : A) v) := by
    change (σ a * σ k) v = (σ k * σ (k⁻¹ * a * k)) v
    rw [← map_mul, ← map_mul]
    congr 2
    group
  rw [this, hv, map_smul]

omit [FiniteDimensional ℂ W] in
theorem map_wt_eq (k : K) (χ : A → ℂ) :
    (wt σ A χ).map (act σ k : W →ₗ[ℂ] W) = wt σ A (k • χ) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact mapsTo_smul σ A k χ hv
  · intro v hv
    refine ⟨σ k⁻¹ v, ?_, ?_⟩
    · have := mapsTo_smul σ A k⁻¹ (k • χ) hv
      rwa [smul_smul, inv_mul_cancel, one_smul] at this
    · change σ k (σ k⁻¹ v) = v
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- `σ k` as a linear equivalence `wt σ A χ ≃ wt σ A (k • χ)`. -/
def wtEquiv (k : K) (χ : A → ℂ) : wt σ A χ ≃ₗ[ℂ] wt σ A (k • χ) :=
  LinearEquiv.ofSubmodules (act σ k) _ _ (map_wt_eq σ A k χ)

omit [FiniteDimensional ℂ W] in
theorem wtEquiv_apply (k : K) (χ : A → ℂ) (v : wt σ A χ) :
    ((wtEquiv σ A k χ v : wt σ A (k • χ)) : W) = σ k v := rfl

omit [FiniteDimensional ℂ W] in
theorem wtEquiv_symm_apply (k : K) (χ : A → ℂ) (v : wt σ A (k • χ)) :
    (((wtEquiv σ A k χ).symm v : wt σ A χ) : W) = σ k⁻¹ v := rfl

omit [FiniteDimensional ℂ W] in
theorem wt_smul_ne_bot_iff (k : K) (χ : A → ℂ) : wt σ A (k • χ) ≠ ⊥ ↔ wt σ A χ ≠ ⊥ := by
  rw [← map_wt_eq]
  exact not_congr ((Submodule.map_injective_of_injective (act σ k).injective).eq_iff'
    (Submodule.map_bot _))

omit [FiniteDimensional ℂ W] in
theorem trace_restrict_conj (k g : K) (χ : A → ℂ)
    (hg : Set.MapsTo (σ (k⁻¹ * g * k)) (wt σ A χ) (wt σ A χ))
    (hg' : Set.MapsTo (σ g) (wt σ A (k • χ)) (wt σ A (k • χ))) :
    LinearMap.trace ℂ _ ((σ g).restrict hg') =
      LinearMap.trace ℂ _ ((σ (k⁻¹ * g * k)).restrict hg) := by
  have : (σ g).restrict hg' = (wtEquiv σ A k χ).conj ((σ (k⁻¹ * g * k)).restrict hg) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      wtEquiv_apply]
    change σ g v = σ k (σ (k⁻¹ * g * k) (((wtEquiv σ A k χ).symm v : wt σ A χ) : W))
    rw [wtEquiv_symm_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [this, LinearMap.trace_conj']

omit [FiniteDimensional ℂ W] in
theorem mapsTo_of_smul_eq {χ : A → ℂ} {h : K} (hh : h • χ = χ) :
    Set.MapsTo (σ h) (wt σ A χ) (wt σ A χ) := by
  have := mapsTo_smul σ A h χ
  rwa [hh] at this

/-- The representation of a subgroup `H₁` fixing `χ` on the weight space `wt σ A χ`. -/
def stabRep (χ : A → ℂ) (H₁ : Subgroup K) (hH₁ : ∀ h ∈ H₁, h • χ = χ) :
    Representation ℂ H₁ (wt σ A χ) :=
  Representation.subrepresentation (σ.comp H₁.subtype) (wt σ A χ)
    (fun h _ hv => mapsTo_of_smul_eq σ A (hH₁ h h.2) hv)

omit [FiniteDimensional ℂ W] in
theorem stabRep_apply (χ : A → ℂ) (H₁ : Subgroup K) (hH₁ : ∀ h ∈ H₁, h • χ = χ) (h : H₁) :
    stabRep σ A χ H₁ hH₁ h = (σ h).restrict (mapsTo_of_smul_eq σ A (hH₁ h h.2)) := rfl

end Rep

section Trace

variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
theorem mapsTo_of_eq {ι : Type*} {N : ι → Submodule ℂ W} {f : W →ₗ[ℂ] W} {i j : ι}
    (hf : Set.MapsTo f (N i) (N j)) (h : j = i) : Set.MapsTo f (N i) (N i) := h ▸ hf

/-- The trace of a map `f` sending each summand `N i` of an internal direct sum into `N (π i)` is
the sum, over the summands with `π i = i` (among a finite set `s` containing all nonzero ones), of
the traces of the restrictions of `f`. -/
theorem trace_eq_sum_fixed {ι : Type*} [DecidableEq ι] {N : ι → Submodule ℂ W}
    (h : DirectSum.IsInternal N)
    (s : Finset ι) (hs : ∀ i, N i ≠ ⊥ → i ∈ s) (π : ι → ι) (f : W →ₗ[ℂ] W)
    (hf : ∀ i, Set.MapsTo f (N i) (N (π i))) :
    LinearMap.trace ℂ W f =
      ∑ i ∈ s, if hi : π i = i then LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi))
        else 0 := by

  have hN : {i | N i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep h.submodule_iSupIndep
  set s₀ := hN.toFinset with hs₀
  have hmem₀ : ∀ i, i ∈ s₀ ↔ N i ≠ ⊥ := fun i => by simp [hs₀]

  have hzero : ∀ i, N i = ⊥ →
      (if hi : π i = i then LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi))
        else 0) = 0 := by
    intro i hi
    split_ifs with hπ
    · have : Subsingleton (N i) := by
        rw [hi]; infer_instance
      rw [Subsingleton.elim (f.restrict (mapsTo_of_eq (hf i) hπ)) 0, map_zero]
    · rfl
  have hsum : (∑ i ∈ s, if hi : π i = i then
        LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi)) else 0) =
      ∑ i ∈ s₀, if hi : π i = i then
        LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi)) else 0 := by
    apply (Finset.sum_subset _ _).symm
    · intro i hi
      exact hs i ((hmem₀ i).1 hi)
    · intro i _ hi
      apply hzero
      by_contra hne
      exact hi ((hmem₀ i).2 hne)
  rw [hsum]

  replace h : DirectSum.IsInternal fun i : s₀ => N i := by
    convert DirectSum.isInternal_ne_bot_iff.mpr h <;> simp [hs₀]
  let κ := fun i : ι => Fin (Module.finrank ℂ (N i))
  let b : (i : s₀) → Basis (κ i) ℂ (N i) := fun i => Module.finBasis ℂ (N i)
  rw [LinearMap.trace_eq_matrix_trace ℂ (h.collectedBasis b), Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort s₀]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hπ : π (i : ι) = i
  · rw [dite_eq_left hπ, LinearMap.trace_eq_matrix_trace ℂ (b i), Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      DirectSum.IsInternal.collectedBasis_coe]
    have hx : f (b i k) ∈ N i := mapsTo_of_eq (hf i) hπ (b i k).2
    rw [h.collectedBasis_repr_of_mem b hx]
    congr 2
  · rw [dite_eq_right hπ]
    apply Finset.sum_eq_zero
    intro k _
    rw [LinearMap.toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
    have hx : f (b i k) ∈ N (π i) := hf i (b i k).2
    by_cases hπs : π (i : ι) ∈ s₀
    · have hne : (⟨π i, hπs⟩ : s₀) ≠ i := fun heq => hπ (congrArg Subtype.val heq)
      exact h.collectedBasis_repr_of_mem_ne b hne hx
    · have hbot : N (π i) = ⊥ := by
        by_contra hne; exact hπs ((hmem₀ _).2 hne)
      rw [hbot, Submodule.mem_bot] at hx
      simp [hx]

end Trace

end Langlands.FiniteRep.WeightSpaces

end
