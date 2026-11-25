/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget

/-! # Lifting maps from finitely presented modules locally

Source: Stacks Project, Modules on Sites, Tag 093T, the finite presentation argument.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] {M N : ModuleCat.{w} Λ}
  {P : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (η : (Functor.const Cᵒᵖ).obj N ⟶ P)

/-- The sieve on which a linear map to sections lifts to the constant source of `η`. -/
def linearLiftSieve {U : Cᵒᵖ} (a : M ⟶ P.obj U) : Sieve U.unop where
  arrows V f := ∃ g : M →ₗ[Λ] N, ∀ x, η.app (op V) (g x) = P.map f.op (a x)
  downward_closed {V W} f hf k := by
    obtain ⟨g, hg⟩ := hf
    refine ⟨g, fun x ↦ ?_⟩
    have hn := NatTrans.naturality_apply η k.op (g x)
    change η.app (op W) (g x) = P.map k.op (η.app (op V) (g x)) at hn
    rw [hn, hg, op_comp, Functor.map_comp, ModuleCat.comp_apply]

/-- Finite presentation makes local lifts of generators descend through all relations. -/
theorem finitePresentation_linearLiftSieve_mem [Module.FinitePresentation Λ M]
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]
    {U : Cᵒᵖ} (a : M ⟶ P.obj U) : linearLiftSieve η a ∈ J U.unop := by
  classical
  obtain ⟨s, hs, hK⟩ := Module.FinitePresentation.out (R := Λ) (M := M)
  let p : (s →₀ Λ) →ₗ[Λ] M := Finsupp.linearCombination Λ (Subtype.val : s → M)
  have hp : Function.Surjective p := by
    apply LinearMap.range_eq_top.mp
    simpa [p, Finsupp.range_linearCombination] using hs
  let Si (i : s) : Sieve U.unop := Presheaf.imageSieve η (a i)
  have hSi (i : s) : Si i ∈ J U.unop := Presheaf.imageSieve_mem J η (a i)
  apply J.transitive (J.finsetInf_mem Finset.univ Si hSi)
  intro V f hf
  have hfi (i : s) : ∃ n : N, η.app (op V) n = P.map f.op (a i) :=
    Finset.inf_le (Finset.mem_univ i) (f := Si) f hf
  choose n hn using hfi
  let q : (s →₀ Λ) →ₗ[Λ] N := Finsupp.linearCombination Λ n
  have hq : (η.app (op V)).hom.comp q = (P.map f.op).hom.comp (a.hom.comp p) := by
    apply Finsupp.lhom_ext
    intro i r
    simpa [q, p, Finsupp.linearCombination_single] using
      congrArg (fun z : P.obj (op V) ↦ r • z) (hn i)
  obtain ⟨t, ht⟩ := hK
  have hrel (r : t) : p r = 0 := by
    apply (LinearMap.mem_ker).1
    rw [← ht]
    exact Submodule.subset_span r.2
  have hzero (r : t) : η.app (op V) (q r) = η.app (op V) 0 := by
    have hh := LinearMap.congr_fun hq r
    simpa [hrel r] using hh
  let Ti (r : t) : Sieve V := Presheaf.equalizerSieve
    (F := (Functor.const Cᵒᵖ).obj N) (X := op V) (q r) 0
  have hTi (r : t) : Ti r ∈ J V := Presheaf.equalizerSieve_mem J η (q r) 0 (hzero r)
  apply J.superset_covering _ (J.finsetInf_mem Finset.univ Ti hTi)
  intro W k hk
  have hk' (r : t) : q r = 0 := Finset.inf_le (Finset.mem_univ r) (f := Ti) k hk
  have hker : LinearMap.ker p ≤ LinearMap.ker q := by
    rw [← ht, Submodule.span_le]
    intro r hr
    exact hk' ⟨r, hr⟩
  let g : M →ₗ[Λ] N :=
    ((LinearMap.ker p).liftQ q hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hgp (z : s →₀ Λ) : g (p z) = q z := by
    simp [g, LinearMap.quotKerEquivOfSurjective_symm_apply]
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := hp x
  rw [hgp]
  have hn' := NatTrans.naturality_apply η k.op (q z)
  change η.app (op W) (q z) = P.map k.op (η.app (op V) (q z)) at hn'
  have hqz : η.app (op V) (q z) = P.map f.op (a (p z)) := LinearMap.congr_fun hq z
  rw [hn', hqz, op_comp, Functor.map_comp, ModuleCat.comp_apply]

end CategoryTheory
