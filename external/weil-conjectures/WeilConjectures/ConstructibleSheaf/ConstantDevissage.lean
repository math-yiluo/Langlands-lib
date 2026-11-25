/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Dévissage of constant sheaves to simple modules

Let `Λ` be a finite ring and `P` a property of objects of the derived category of étale sheaves
of `Λ`-modules on a scheme `V` which holds for zero objects, is invariant under isomorphisms and
stable under extensions in distinguished triangles. If `P` holds for the constant sheaves
`S_V` (placed in degree `0`) at the simple `Λ`-modules `S`, it holds for the constant sheaf `N_V`
at every finite `Λ`-module `N`: a nonzero finite module has a simple submodule `S`, and the short
exact sequence `0 ⟶ S ⟶ N ⟶ N ⧸ S ⟶ 0` gives a short exact sequence of constant sheaves, hence a
distinguished triangle.

## Main statements

- `AlgebraicGeometry.Scheme.constantSheaf_induction`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.Scheme

variable {V : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]

/-- **Dévissage of constant sheaves to simple modules.** A property of the derived category of
étale sheaves of `Λ`-modules, `Λ` a finite ring, which holds for zero objects, is invariant
under isomorphisms and stable under extensions in distinguished triangles, and holds for the
constant sheaves at simple modules, holds for the constant sheaf at every finite module. -/
theorem constantSheaf_induction
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) → Prop)
    (hzero : ∀ K, IsZero K → P K)
    (hext : ∀ T ∈ distTriang (DerivedCategory (Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))), P T.obj₁ → P T.obj₃ → P T.obj₂)
    (hsimple : ∀ (S : ModuleCat.{u + 1} Λ) [Finite S], IsSimpleModule Λ S →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj S)))
    (N : ModuleCat.{u + 1} Λ) [Finite N] :
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)) := by
  induction h : Nat.card N using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  subst h
  by_cases hN : Subsingleton N
  · refine hzero _ (Functor.map_isZero _ (Functor.map_isZero _ ?_))
    exact ModuleCat.isZero_of_subsingleton N
  · rw [not_subsingleton_iff_nontrivial] at hN
    have : IsArtinian Λ N := inferInstance
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule Λ N)
    have hSs : IsSimpleModule Λ S := isSimpleModule_iff_isAtom.2 hS
    have : Finite (N ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
    let sc : ShortComplex (ModuleCat.{u + 1} Λ) :=
      ShortComplex.mk (ModuleCat.ofHom S.subtype) (ModuleCat.ofHom S.mkQ) (by
        ext x
        simp)
    have hsc : sc.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
        intro x hx
        simp only [sc, ModuleCat.hom_ofHom, LinearMap.mem_ker, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · exact (ModuleCat.mono_iff_injective _).2 S.injective_subtype
      · exact (ModuleCat.epi_iff_surjective _).2 S.mkQ_surjective
    have hsc' := constantEtaleSheaf_shortExact V Λ sc hsc
    have hS0 : S ≠ ⊥ := hS.1
    have hlt : Nat.card (N ⧸ S) < Nat.card N := by
      have := Submodule.card_eq_card_quotient_mul_card S
      have h1 : 1 < Nat.card S := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact Submodule.nontrivial_iff_ne_bot.2 hS0
      have h2 : 0 < Nat.card (N ⧸ S) := Nat.card_pos
      nlinarith
    have hQ := ih _ hlt (ModuleCat.of Λ (N ⧸ S)) rfl
    have hS' := hsimple (ModuleCat.of Λ S) hSs
    exact hext _ hsc'.singleTriangle_distinguished hS' hQ

end AlgebraicGeometry.Scheme
