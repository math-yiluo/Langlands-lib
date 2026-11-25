/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.SiteCechFreeComplexExactAux
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Free module chains on chosen site Čech products

Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteCechComplex

variable {C : Type u} [Category.{v} C] {T : Type v} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)

/-- The free Čech chain complex is exact in every positive degree, without a covering.
Source: Stacks Project, Cohomology on Sites, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-site-cech-free-complex-exact)

Proof: evaluate at an object X. A basis element is a pair (t,a), with t an
(n+1)-tuple of indices and a:X→W(n,t). Partition these elements by
φ = a ≫ pr(n,t,0) ≫ hom(t(0)). The product universal property identifies
that fibre with (n+1)-tuples from Lφ = Σ i, {b:X→f(i) | b≫hom(i)=φ}.
The inverse is the unique product lift of the component maps. The indexMap_pr
law says that each face deletes its indexed component, so this identification
respects the alternating boundary and the R(X)-linear extension to free modules.
The free module on this disjoint union is the direct sum of the tuple complexes
on Lφ. Empty Lφ contributes zero. For nonempty Lφ choose one lift and insert
it as the first coordinate; powerSetComplex_contractible gives exactness at
n+1, including n=0. Direct sums preserve exactness for modules. Finally
module-presheaf kernels and cokernels are objectwise, so evaluation jointly
reflects exactness. All basis sets and free module values lie in universe v;
no natural choice of a lift across objects is needed. -/
theorem freeComplex_exactAt (R : Cᵒᵖ ⥤ RingCat.{v}) (n : ℕ) :
    (S.freeComplex R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  let L := (S.freeComplex R).sc' (n + 2) (n + 1) n
  have he (X : Cᵒᵖ) : (L.map (PresheafOfModules.evaluation R X)).Exact := by
    obtain ⟨h, k, hk⟩ := freeComplex_evaluation_contracting S R n X
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨h x, ?_⟩
    have hid := ConcreteCategory.congr_hom hk x
    change ((S.freeComplex R).d (n + 1) n).app X x = 0 at hx
    change ((S.freeComplex R).d (n + 2) (n + 1)).app X (h x) +
      k (((S.freeComplex R).d (n + 1) n).app X x) = x at hid
    change ((S.freeComplex R).d (n + 2) (n + 1)).app X (h x) = x
    simpa only [hx, map_zero, add_zero] using hid
  rw [ShortComplex.exact_iff_isZero_homology]
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro X
  have hz : IsZero ((PresheafOfModules.evaluation R X).obj L.homology) :=
    ((L.mapHomologyIso (PresheafOfModules.evaluation R X)).isZero_iff).mp
      ((L.map (PresheafOfModules.evaluation R X)).exact_iff_isZero_homology.mp (he X))
  exact hz.eq_of_src _ _

end CategoryTheory.SiteCechComplex
