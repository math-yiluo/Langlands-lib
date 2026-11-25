/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Presentation.Tensor
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of presentations of modules

Given relations `ρ : Module.Relations A` and a ring homomorphism `f : A →+* B`, we define the
base changed relations `ρ.baseChange f : Module.Relations B`, with the same generators and
relations and coefficients mapped along `f`. If `s : ρ.Solution M` is a presentation of the
`A`-module `M`, then `1 ⊗ s` is a presentation of `B ⊗[A] M` by the base changed relations
(`Module.Relations.Solution.IsPresentation.baseChange`).
-/

@[expose] public noncomputable section

universe w' w₀ w₁ u v w

open TensorProduct

namespace Module.Relations

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The base change of relations along a ring homomorphism `f : A →+* B`: the same generators
and relations, with the coefficients mapped along `f`. -/
abbrev baseChange (ρ : Relations.{w₀, w₁} A) (f : A →+* B) : Relations.{w₀, w₁} B where
  G := ρ.G
  R := ρ.R
  relation r := Finsupp.mapRange f f.map_zero (ρ.relation r)

lemma baseChange_relation (ρ : Relations.{w₀, w₁} A) (f : A →+* B) (r : ρ.R) :
    (ρ.baseChange f).relation r = Finsupp.mapRange f f.map_zero (ρ.relation r) :=
  rfl

/-- Linear combinations with coefficients mapped along a ring homomorphism `f : A →+* B` are
linear combinations with the original coefficients, if `A` acts through `f`. -/
lemma linearCombination_mapRange_of_smul_eq (f : A →+* B) {G N : Type*} [AddCommGroup N]
    [Module A N] [Module B N] (hf : ∀ (a : A) (n : N), a • n = f a • n) (v : G → N)
    (x : G →₀ A) :
    Finsupp.linearCombination B v (Finsupp.mapRange f f.map_zero x) =
      Finsupp.linearCombination A v x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.mapRange_add (map_add _), map_add, map_add, hx, hy]
  | single g a => simp [hf]

/-- Linear combinations with coefficients mapped along `algebraMap A B` are linear combinations
with the original coefficients. -/
lemma linearCombination_mapRange_algebraMap [Algebra A B] {G : Type*} {N : Type*}
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (v : G → N) (x : G →₀ A) :
    Finsupp.linearCombination B v (Finsupp.mapRange (algebraMap A B) (map_zero _) x) =
      Finsupp.linearCombination A v x :=
  linearCombination_mapRange_of_smul_eq _ (fun a n ↦ (algebraMap_smul B a n).symm) v x

variable [Algebra A B] {ρ : Relations.{w₀, w₁} A} {M : Type w} [AddCommGroup M] [Module A M]

namespace Solution

/-- A solution of `ρ` in a `B`-module `N`, viewed as an `A`-module, obtained from a solution of
the base changed relations. -/
@[simps]
def ofBaseChange {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (t : (ρ.baseChange (algebraMap A B)).Solution N) : ρ.Solution N where
  var := t.var
  linearCombination_var_relation r := by
    rw [← linearCombination_mapRange_algebraMap (B := B)]
    exact t.linearCombination_var_relation r

/-- The base change `1 ⊗ s` of a solution `s` of `ρ` in `M`, a solution of the base changed
relations in `B ⊗[A] M`. -/
@[simps]
def baseChange (s : ρ.Solution M) : (ρ.baseChange (algebraMap A B)).Solution (B ⊗[A] M) where
  var g := (1 : B) ⊗ₜ s.var g
  linearCombination_var_relation r := by
    have h₁ := linearCombination_mapRange_algebraMap (B := B)
      ((TensorProduct.mk A B M 1) ∘ s.var) (ρ.relation r)
    rw [← Finsupp.apply_linearCombination, s.linearCombination_var_relation, map_zero] at h₁
    exact h₁

namespace IsPresentation

variable {s : ρ.Solution M} (h : s.IsPresentation)
include h

/-- The universal property of the base change `1 ⊗ s` of a presentation `s`. -/
noncomputable def isPresentationCoreBaseChange :
    IsPresentationCore.{w'} (s.baseChange (B := B)) where
  desc {N} _ _ t :=
    let : Module A N := Module.compHom N (algebraMap A B)
    have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    (h.desc t.ofBaseChange).liftBaseChange B
  postcomp_desc {N} _ _ t := by
    let : Module A N := Module.compHom N (algebraMap A B)
    have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    ext g
    simp
  postcomp_injective {N} _ _ f f' h' := by
    let : Module A N := Module.compHom N (algebraMap A B)
    have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have key : (f.restrictScalars A).comp (TensorProduct.mk A B M 1) =
        (f'.restrictScalars A).comp (TensorProduct.mk A B M 1) :=
      h.postcomp_injective (Solution.ext (funext fun g ↦ by
        have := congr_var h' g
        simpa using this))
    refine TensorProduct.AlgebraTensorModule.ext fun b m ↦ ?_
    have hm := LinearMap.congr_fun key m
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      TensorProduct.mk_apply] at hm
    rw [← mul_one b, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, hm]

/-- **Base change of a presentation.** If `s` is a presentation of the `A`-module `M` by the
relations `ρ`, then `1 ⊗ s` is a presentation of `B ⊗[A] M` by the base changed relations. -/
theorem baseChange : (s.baseChange (B := B)).IsPresentation :=
  (isPresentationCoreBaseChange h).isPresentation

end IsPresentation

section RingHom

variable {B' : Type*} [CommRing B'] {f : A →+* B'} [Module B' M]
  (hf : ∀ (a : A) (m : M), a • m = f a • m)

/-- A solution of `ρ` in `M` is a solution of the relations base changed along `f : A →+* B'`,
if `M` is a `B'`-module on which `A` acts through `f`. -/
@[simps]
def ofSMulEq (s : ρ.Solution M) : (ρ.baseChange f).Solution M where
  var := s.var
  linearCombination_var_relation r :=
    (linearCombination_mapRange_of_smul_eq f hf s.var (ρ.relation r)).trans
      (s.linearCombination_var_relation r)

include hf in
/-- A presentation of `M` over `A` is a presentation over `B'` by the base changed relations, if
`A` acts on `M` through a surjective ring homomorphism `f : A →+* B'`. -/
theorem IsPresentation.ofSMulEq {s : ρ.Solution M} (hs : s.IsPresentation)
    (hsurj : Function.Surjective f) : (s.ofSMulEq hf).IsPresentation := by
  rw [isPresentation_iff] at hs ⊢
  obtain ⟨h₁, h₂⟩ := hs
  have hπ (x : ρ.G →₀ A) :
      (s.ofSMulEq hf).π (Finsupp.mapRange f f.map_zero x) = s.π x :=
    linearCombination_mapRange_of_smul_eq f hf s.var x
  refine ⟨eq_top_iff.mpr fun x hx₀ ↦ ?_, le_antisymm (fun y hy ↦ ?_) ?_⟩
  · have hx : x ∈ Submodule.span A (Set.range s.var) := h₁ ▸ Submodule.mem_top
    clear hx₀
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hf a x ▸ Submodule.smul_mem _ _ hx
  · obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective f f.map_zero hsurj y
    have hx : x ∈ LinearMap.ker s.π := by
      rw [LinearMap.mem_ker, ← hπ]
      exact hy
    clear hy
    rw [h₂] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact Submodule.subset_span ⟨r, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Finsupp.mapRange_add (map_add f)]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Finsupp.mapRange_smul' a (f a) x (map_mul f a)]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun r ↦ ?_)
    change (s.ofSMulEq hf).π (Finsupp.mapRange f f.map_zero (ρ.relation r)) = 0
    rw [hπ]
    exact s.π_relation r

end RingHom

/-- Transport a solution along a pointwise equality of the coefficients of the relations. -/
@[simps]
def ofRelationEq {ρ₁ : Relations.{w₀, w₁} A} {c : ρ₁.R → ρ₁.G →₀ A}
    (h : ∀ r, ρ₁.relation r = c r) (s : ρ₁.Solution M) :
    (Relations.mk ρ₁.G ρ₁.R c).Solution M where
  var := s.var
  linearCombination_var_relation r := by
    change Finsupp.linearCombination A s.var (c r) = 0
    rw [← h r]
    exact s.linearCombination_var_relation r

/-- Transporting a presentation along a pointwise equality of the coefficients of the relations
gives a presentation. -/
theorem IsPresentation.ofRelationEq {ρ₁ : Relations.{w₀, w₁} A} {c : ρ₁.R → ρ₁.G →₀ A}
    (h : ∀ r, ρ₁.relation r = c r) {s : ρ₁.Solution M} (hs : s.IsPresentation) :
    (s.ofRelationEq h).IsPresentation := by
  obtain rfl : c = ρ₁.relation := funext fun r ↦ (h r).symm
  exact hs

end Solution

end Module.Relations
