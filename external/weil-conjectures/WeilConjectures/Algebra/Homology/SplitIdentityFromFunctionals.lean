/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Projection
import WeilConjectures.Algebra.Homology.SplitSubmodulesStable

/-!
# Assembling cancellation from two split functionals

Source: Stacks Project, Algebra, Tag 00MT, proof, final three sentences.
(blueprint: lem-weil-pbc-split-identity-from-functionals).
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace ChainComplex

private theorem kernel_span_isCompl {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a : M →ₗ[R] R) (z : M) (hz : a z = 1) :
    IsCompl (LinearMap.ker a) (R ∙ z) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hr : r = 0 := by simpa [hz] using hx
    simp [hr]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x - a x • z, ?_, a x • z, ?_, sub_add_cancel _ _⟩
    · simp [LinearMap.mem_ker, hz]
    · exact Submodule.mem_span_singleton.mpr ⟨a x, rfl⟩

private def spanFunctionalEquiv {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a : M →ₗ[R] R) (z : M) (hz : a z = 1) :
    (R ∙ z) ≃ₗ[R] R where
  toFun x := a x
  invFun r := ⟨r • z, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.property
    change a (x : M) • z = (x : M)
    rw [← hr]
    simp [hz]
  right_inv r := by simp [hz]
  map_add' x y := map_add a (x : M) (y : M)
  map_smul' r x := map_smul a r (x : M)

private def boolPiEquiv {R : Type u} [CommRing R]
    (A B : ModuleCat.{v} R) :
    (∀ s : Bool, ↑(if s then B else A)) ≃ₗ[R] A × B where
  toFun p := (p false, p true)
  invFun p := fun s ↦ Bool.casesOn s p.1 p.2
  left_inv p := by funext s; cases s <;> rfl
  right_inv p := rfl
  map_add' p q := rfl
  map_smul' r p := rfl

private noncomputable def submoduleSumEquiv {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (S U : Submodule R M) (h : IsCompl S U) :
    (⨁ s : Bool, ↑(if s then ModuleCat.of R U else ModuleCat.of R S)) ≃ₗ[R] M :=
  (DirectSum.linearEquivFunOnFintype R Bool _).trans
    ((boolPiEquiv (ModuleCat.of R S) (ModuleCat.of R U)).trans (S.prodEquivOfIsCompl U h))

private theorem submoduleSumEquiv_apply {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (S U : Submodule R M) (h : IsCompl S U)
    (x : S) (t : U) :
    submoduleSumEquiv S U h
      (DirectSum.lof R Bool (fun s ↦ ↑(if s then ModuleCat.of R U else ModuleCat.of R S)) false x +
        DirectSum.lof R Bool (fun s ↦ ↑(if s then ModuleCat.of R U else ModuleCat.of R S)) true t) =
      (x : M) + (t : M) := by
  dsimp [submoduleSumEquiv, boolPiEquiv, DirectSum.lof, DFinsupp.lsingle]
  change (x : M) + 0 + (0 + (t : M)) = (x : M) + (t : M)
  simp

set_option linter.unusedVariables false in
/-- Assemble the complement and identity complex once the neighboring maps respect the split.
Source: Stacks Project, Algebra, Tag 00MT, proof, final three sentences.
(blueprint: lem-weil-pbc-split-identity-from-functionals).

Proof: Let the complementary terms be `ker α`, `ker β` at `i`, `i - 1`, and the original
terms elsewhere. The equality `β ∘ d = α` restricts the middle differential to these
kernels; `hin` restricts the incoming differential; all other differentials restrict
without a codomain change. The restricted differentials square to zero by the original
complex relation and injectivity of submodule inclusions. Let `T` have a universe lift of
`R` at `i`, `i - 1`, zero terms elsewhere and the identity as middle differential.
The degreewise decompositions are `x = (x - α(x) • z) + α(x) • z` at `i` and
`y = (y - β(y) • w) + β(y) • w` at `i - 1`; the kernel components are unique since
`α(z) = β(w) = 1`. Use these decompositions to make the degreewise binary-direct-sum
linear equivalences. In degree `i + 1` compatibility is `hin`; in degree `i` it follows
from `hd` and `hdz`; in degree `i - 1` it is `hout`; in all other degrees it is the
identity. No finiteness or freeness is required, and the construction includes the zero
ring. The displayed equivalences `g` identify the complement with these exact submodules. -/
theorem exists_splitting_of_split_functionals
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (α : C.X i →ₗ[R] R) (β : C.X (i - 1) →ₗ[R] R)
    (z : C.X i) (w : C.X (i - 1))
    (hz : α z = 1) (hw : β w = 1)
    (hd : ∀ x, β ((C.d i (i - 1)).hom x) = α x)
    (hdz : (C.d i (i - 1)).hom z = w)
    (hin : ∀ x, α ((C.d (i + 1) i).hom x) = 0)
    (hout : (C.d (i - 1) (i - 2)).hom w = 0) :
    let S : ∀ j : ℤ, Submodule R (C.X j) := fun j ↦
      if h : j = i then h ▸ LinearMap.ker α
      else if h : j = i - 1 then h ▸ LinearMap.ker β else ⊤
    ∃ (C' T : ChainComplex (ModuleCat.{max u v} R) ℤ)
      (g : ∀ j, C'.X j ≃ₗ[R] S j),
      (∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j)) ∧
      ∃ (e : T.X i ≃ₗ[R] R) (f : T.X (i - 1) ≃ₗ[R] R),
        (∀ t : T.X i, f ((T.d i (i - 1)).hom t) = e t) ∧
        let M : ℤ → Bool → ModuleCat.{max u v} R :=
          fun j s ↦ if s then T.X j else C'.X j
        ∃ ψ : ∀ j : ℤ, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j,
          ∀ (j : ℤ) (x : C'.X j) (t : T.X j),
            (C.d j (j - 1)).hom
                (ψ j (DirectSum.lof R Bool (fun s ↦ M j s) false x +
                  DirectSum.lof R Bool (fun s ↦ M j s) true t)) =
              ψ (j - 1)
                (DirectSum.lof R Bool (fun s ↦ M (j - 1) s) false
                    ((C'.d j (j - 1)).hom x) +
                  DirectSum.lof R Bool (fun s ↦ M (j - 1) s) true
                    ((T.d j (j - 1)).hom t)) := by
  classical
  let S := splitKernelTerms C i α β
  let U := splitLineTerms C i z w
  obtain ⟨hS, hU⟩ := split_submodules_stable C i α β z w hd hdz hin hout
  let C' := restrictToSubmodules C S hS
  let T := restrictToSubmodules C U hU
  have hi : i ≠ i - 1 := by omega
  have hSi : S i = LinearMap.ker α := by simp [S, splitKernelTerms]
  have hUi : U i = R ∙ z := by simp [U, splitLineTerms]
  have hSprev : S (i - 1) = LinearMap.ker β := by
    simp [S, splitKernelTerms, Ne.symm hi]
  have hUprev : U (i - 1) = R ∙ w := by
    simp [U, splitLineTerms, Ne.symm hi]
  have hcompl : ∀ j, IsCompl (S j) (U j) := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [hSi, hUi]
      exact kernel_span_isCompl α z hz
    by_cases hjprev : j = i - 1
    · subst j
      rw [hSprev, hUprev]
      exact kernel_span_isCompl β w hw
    simpa [S, U, splitKernelTerms, splitLineTerms, hji, hjprev] using
      (isCompl_top_bot : IsCompl (⊤ : Submodule R (C.X j)) ⊥)
  have hT : ∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j) := by
    intro j hj hj'
    change Subsingleton (U j)
    have hzero : U j = ⊥ := by simp [U, splitLineTerms, hj, hj']
    rw [hzero]
    infer_instance
  let e : T.X i ≃ₗ[R] R :=
    (LinearEquiv.ofEq (U i) (R ∙ z) hUi).trans (spanFunctionalEquiv α z hz)
  let f : T.X (i - 1) ≃ₗ[R] R :=
    (LinearEquiv.ofEq (U (i - 1)) (R ∙ w) hUprev).trans (spanFunctionalEquiv β w hw)
  have he : ∀ t : T.X i, e t = α (t : U i).val := by
    intro t
    rfl
  have hf : ∀ t : T.X (i - 1), f t = β (t : U (i - 1)).val := by
    intro t
    rfl
  refine ⟨C', T, (fun j ↦ LinearEquiv.refl R (S j)), hT, e, f, ?_, ?_⟩
  · intro t
    rw [he, hf]
    exact hd (t : U i).val
  · refine ⟨(fun j ↦ submoduleSumEquiv (S j) (U j) (hcompl j)), ?_⟩
    intro j x t
    dsimp only [C', T, restrictToSubmodules] at x t ⊢
    rw [submoduleSumEquiv_apply, submoduleSumEquiv_apply, map_add]
    rfl

end ChainComplex
