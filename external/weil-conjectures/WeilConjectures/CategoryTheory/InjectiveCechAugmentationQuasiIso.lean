/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.SmallInjectivePresheafCechExact
import WeilConjectures.CategoryTheory.SheafCechAugmentationDegreeZero
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The canonical augmented Čech row of an injective sheaf

Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The restriction augmentation of one injective sheaf is a quasi-isomorphism.
The Hom sets, covering index, and abelian group values all have universe v.
Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6; blueprint
lemma-coherent-base-change-invertible-sheaves--1, Step 3.
(blueprint: lem-sc-injective-cech-augmentation-quasi-iso)

Proof: Form the augmented complex of free abelian presheaves represented by the
iterated fibre products of the covering. Its terms are v-small-valued: each
representable has v-small Hom sets, and the tuple-index sets are v-small. After
sheafification the complex is exact. Indeed, a section of the covering sieve
locally lifts to one of the covering members. On such a localization, insert this
member at the front of each tuple to contract the augmented simplicial complex.
Exactness can be checked locally, so these local contractions prove exactness
of the sheafified augmented complex. Applying Hom into the injective sheaf is
exact. The free abelian representable adjunction identifies these Hom groups
with sections on the fibre products, and takes the simplicial boundary to the
alternating restriction differential. The sheaf condition identifies the kernel
in degree zero with sections on X by the canonical restriction map; positive
cohomology is zero by the preceding exactness argument. The categorical products
in Mathlib are the same section products through their projection universal
property. The displayed component condition fixes the augmentation to this
restriction map, so it induces precisely that degree-zero isomorphism. At all
positive degrees both homology objects are zero. If the covering index is empty,
the sheaf condition forces sections on X to be zero and every Čech term is zero,
so the conclusion still holds. No double complex or totalization is used. -/
theorem injective_cech_augmentation_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (I : Sheaf J AddCommGrpCat.{v}) [Injective I] (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIso e := by
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  refine ⟨fun p ↦ ?_⟩
  cases p with
  | zero => exact sheaf_cech_augmentation_quasiIsoAt_zero I X π hπ e he
  | succ q =>
    rw [quasiIsoAt_iff_exactAt e (q + 1)
      (CochainComplex.exactAt_succ_single_obj _ q)]
    exact small_injective_presheaf_cech_exact I.obj X U π q

end CategoryTheory
