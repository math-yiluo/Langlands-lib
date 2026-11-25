/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

universe u v

namespace ChainComplex

noncomputable def splitKernelTerms
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (α : C.X i →ₗ[R] R) (β : C.X (i - 1) →ₗ[R] R) :
    ∀ j : ℤ, Submodule R (C.X j) := fun j ↦
  if h : j = i then h ▸ LinearMap.ker α
  else if h : j = i - 1 then h ▸ LinearMap.ker β else ⊤

noncomputable def splitLineTerms
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (z : C.X i) (w : C.X (i - 1)) : ∀ j : ℤ, Submodule R (C.X j) := fun j ↦
  if h : j = i then h ▸ (R ∙ z)
  else if h : j = i - 1 then h ▸ (R ∙ w) else ⊥

/-- The kernel terms and the explicitly generated line terms are invariant under the differential.
Source: Stacks Project, Algebra, Tag 00MT, proof, final three sentences.
(blueprint: lem-weil-pbc-split-submodules-stable).

Proof: Off the chain shape the differential is zero, so its image belongs to every submodule.
For a differential j → j - 1, the kernel condition is nontrivial only when its target is i
or i - 1. In the first case hin applies, and in the second hd sends ker α into ker β.
All other targets have top kernel term. For the line terms, an element at i is r • z and
its image is r • w by hdz. An element at i - 1 is r • w and its image is zero by hout.
At every other source the line term is bottom, so its image is zero. This proof works
also for the zero ring; no claim of a nonzero generator is used. -/
theorem split_submodules_stable
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (i : ℤ) (α : C.X i →ₗ[R] R) (β : C.X (i - 1) →ₗ[R] R)
    (z : C.X i) (w : C.X (i - 1))
    (hd : ∀ x, β ((C.d i (i - 1)).hom x) = α x)
    (hdz : (C.d i (i - 1)).hom z = w)
    (hin : ∀ x, α ((C.d (i + 1) i).hom x) = 0)
    (hout : (C.d (i - 1) (i - 2)).hom w = 0) :
    (∀ j k (x : C.X j), x ∈ splitKernelTerms C i α β j →
      (C.d j k).hom x ∈ splitKernelTerms C i α β k) ∧
    (∀ j k (x : C.X j), x ∈ splitLineTerms C i z w j →
      (C.d j k).hom x ∈ splitLineTerms C i z w k) := by
  classical
  have hi : i ≠ i - 1 := by omega
  constructor
  · intro j k x hx
    by_cases hshape : (ComplexShape.down ℤ).Rel j k
    · have hjk : k + 1 = j := hshape
      by_cases hk : k = i
      · subst k
        have hj : j = i + 1 := by omega
        clear hjk hshape
        subst j
        simpa [splitKernelTerms] using hin x
      by_cases hk' : k = i - 1
      · subst k
        have hj : j = i := by omega
        clear hjk hshape
        subst j
        have hx' : α x = 0 := by simpa [splitKernelTerms] using hx
        simpa [splitKernelTerms, Ne.symm hi, hd] using hx'
      simp [splitKernelTerms, hk, hk']
    · rw [C.shape j k hshape]
      exact (splitKernelTerms C i α β k).zero_mem
  · intro j k x hx
    by_cases hshape : (ComplexShape.down ℤ).Rel j k
    · have hjk : k + 1 = j := hshape
      by_cases hj : j = i
      · have hk : k = i - 1 := by omega
        clear hjk hshape
        subst j
        subst k
        have hx' : x ∈ R ∙ z := by simpa [splitLineTerms] using hx
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx'
        simpa [splitLineTerms, Ne.symm hi, hdz] using
          (Submodule.mem_span_singleton.mpr ⟨r, rfl⟩ : r • w ∈ R ∙ w)
      by_cases hj' : j = i - 1
      · have hk : k = i - 2 := by omega
        clear hjk hshape
        subst j
        subst k
        have hx' : x ∈ R ∙ w := by simpa [splitLineTerms, Ne.symm hi] using hx
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx'
        rw [map_smul, hout, smul_zero]
        exact (splitLineTerms C i z w (i - 2)).zero_mem
      have hx' : x = 0 := by simpa [splitLineTerms, hj, hj'] using hx
      rw [hx', map_zero]
      exact (splitLineTerms C i z w k).zero_mem
    · rw [C.shape j k hshape]
      exact (splitLineTerms C i z w k).zero_mem

/-- Restrict a complex to an explicitly given family of invariant submodules. -/
def restrictToSubmodules
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℤ)
    (P : ∀ j : ℤ, Submodule R (C.X j))
    (hP : ∀ j k (x : C.X j), x ∈ P j → (C.d j k).hom x ∈ P k) :
    ChainComplex (ModuleCat.{max u v} R) ℤ where
  X j := ModuleCat.of R (P j)
  d j k := ModuleCat.ofHom {
    toFun := fun x ↦ ⟨(C.d j k).hom x, hP j k x x.property⟩
    map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
    map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  shape j k h := by
    apply ModuleCat.hom_ext
    ext x
    change (C.d j k).hom x = 0
    rw [C.shape j k h]
    rfl
  d_comp_d' j k l _ _ := by
    apply ModuleCat.hom_ext
    ext x
    change (C.d k l).hom ((C.d j k).hom x) = 0
    exact congrArg (fun f ↦ f.hom (x : C.X j)) (C.d_comp_d j k l)

end ChainComplex
