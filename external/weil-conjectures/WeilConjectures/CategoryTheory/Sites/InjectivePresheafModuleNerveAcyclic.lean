/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.Sites.PresheafFreeNerveComparison
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Čech nerve acyclicity for injective module presheaves

Source: Stacks Project, Cohomology on Sites, Tags 03FC, 03F5, 03AT.
(blueprint: lem-sc-injective-presheaf-module-nerve-acyclic)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The Čech nerve of any map of small-valued presheaves is acyclic in positive
cochain degrees against an injective module presheaf. No covering condition is needed.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC, using Tags 03F5,
03AS and 03AT; Hypercoverings, Tag 01GC, fibrewise nerve formulation.
(blueprint: lem-sc-injective-presheaf-module-nerve-acyclic)

Proof: apply the free `R`-module presheaf functor to the simplicial nerve of `f`.
At each object, split its basis by the value of `f`. A fibre with no elements
contributes zero in every nerve degree. In every nonempty fibre, prefix a chosen
lift to the tuple. The alternating deletion formula gives a contracting homotopy,
so the free module chain complex is exact in every positive degree. Exactness
of module presheaves is objectwise. All free modules are small-valued, since the
ring and both presheaves have values in the same universe. Thus injectivity of
`M` applies to the image inclusions in this complex. A cocycle factors through
the image of the outgoing boundary, and injectivity extends that factor to the
preceding chain term. Free-module adjunction followed by free-abelian adjunction
identifies these Hom groups with the terms of `presheafCechComplex f M.presheaf`;
the identifications commute with the alternating boundaries. Hence each cocycle
is a coboundary and positive cohomology is zero. -/
theorem injective_presheaf_module_nerve_acyclic
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (M : PresheafOfModules.{v} R) [Injective M]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (q : ℕ) (hq : 0 < q) :
    IsZero ((presheafCechComplex f M.presheaf).homology q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let K := presheafFreeNerveComplex R f
  obtain ⟨e, he⟩ := presheafFreeNerveComplex_comparison R M f
  have hK : (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
      (K.d_comp_d _ _ _)).Exact := by
    exact (HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n
      (by simp) (by simp)).1 (presheafFreeNerveComplex_exactAt R f n)
  have hExact : (presheafCechComplex f M.presheaf).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro c hc
    change ∃ b, (presheafCechComplex f M.presheaf).d n (n + 1) b = c
    let a : K.X (n + 1) ⟶ M := (e (n + 1)).symm c
    have ha : K.d (n + 2) (n + 1) ≫ a = 0 := by
      apply (e (n + 2)).injective
      rw [map_zero]
      change e ((n + 1) + 1) (K.d ((n + 1) + 1) (n + 1) ≫ a) = 0
      rw [he, AddEquiv.apply_symm_apply]
      exact hc
    refine ⟨e n (hK.descToInjective a ha), ?_⟩
    rw [← he, hK.comp_descToInjective a ha]
    exact (e (n + 1)).apply_symm_apply c
  exact hExact.isZero_homology

end CategoryTheory
