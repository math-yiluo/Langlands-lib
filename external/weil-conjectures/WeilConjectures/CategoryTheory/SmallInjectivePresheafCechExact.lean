/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.CategoryTheory.SmallCechFreeComparison
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Positive exactness of the small-valued injective presheaf Čech complex

Source: Stacks Project, Tags 03AS, 03AT and 03AU.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Positive exactness of the categorical Čech complex of a size-aligned injective presheaf.
Source: Stacks Project, Cohomology on Sites, Tags 03AS, 03AT and 03AU.
(blueprint: lem-sc-small-injective-presheaf-cech-exact)

Proof: In degree n form the coproduct of free abelian representables of the products
indexed by Fin (n+1) -> iota. Hom sets and the tuple index are v-small, so these are
presheaves of v-small abelian groups even when the object type of C is larger.
Use the alternating projection boundary. Evaluated at Z, the basis decomposes by
the common composite Z -> X. Each summand is the free abelian tuple complex on
the set of lifts to the family. For an empty lift set every term is zero. Otherwise,
choose a lift and prepend it to tuples; the alternating boundary identity contracts
the complex, proving exactness in all positive chain degrees. Kernels and images
of presheaves are computed objectwise, so the free presheaf complex is exact there.
Apply Hom(-, P): a cocycle factors through the image of the preceding boundary,
and injectivity extends the resulting map from that image to the preceding free
term. This produces a primitive. The free representable adjunction and the product
universal property identify this Hom complex with Mathlib's categorical Čech
complex, including its alternating signs. Thus every positive cocycle is a boundary.
The argument requires no covering, and treats the empty family without exception. -/
theorem small_injective_presheaf_cech_exact
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [Injective P] (X : C)
    {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X) (q : ℕ) :
    ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
      ((Over.forget X).op ⋙ P)).ExactAt (q + 1) := by
  let K := SmallCech.freeComplex X U π
  let e := SmallCech.cochainEquiv X U π P
  let L := (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
    ((Over.forget X).op ⋙ P)
  have hK : (ShortComplex.mk (K.d (q + 2) (q + 1)) (K.d (q + 1) q)
      (K.d_comp_d _ _ _)).Exact :=
    (HomologicalComplex.exactAt_iff' K (q + 2) (q + 1) q
      (by simp) (by simp)).1 (SmallCech.freeComplex_exactAt X U π q)
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro c hc
  let a : K.X (q + 1) ⟶ P := (e (q + 1)).symm c
  have ha : K.d (q + 2) (q + 1) ≫ a = 0 := by
    apply (e (q + 2)).injective
    rw [map_zero]
    change SmallCech.cochainEquiv X U π P ((q + 1) + 1)
      ((SmallCech.freeComplex X U π).d ((q + 1) + 1) (q + 1) ≫ a) = 0
    rw [SmallCech.cochainEquiv_boundary]
    dsimp only [a]
    rw [(e (q + 1)).apply_symm_apply]
    exact hc
  refine ⟨e q (hK.descToInjective a ha), ?_⟩
  change L.d q (q + 1) (e q (hK.descToInjective a ha)) = c
  rw [← SmallCech.cochainEquiv_boundary, hK.comp_descToInjective a ha]
  exact (e (q + 1)).apply_symm_apply c

end CategoryTheory
