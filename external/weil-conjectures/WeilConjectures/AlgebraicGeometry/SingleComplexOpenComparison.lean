/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # The canonical single-complex comparison on a source open

Source: Stacks Project, Tag 0DJ9, source-open induction.
(blueprint: def-pc-single-complex-open-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The comparison for `U → S`, with the given coefficient map restricted to its
cartesian inverse image. All data are constructed from the canonical pullback
composition comparisons; there is no choice of a coefficient object or morphism.
Source: Stacks Project, Tag 0DJ9, the comparison on a quasi-compact open.
(blueprint: def-pc-single-complex-open-comparison). -/
noncomputable def singleComplexOpenComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U : X.Opens) :=
  schemeDerivedBaseChangeMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
    g (pullback.snd g' U.ι)
    (by rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc])
    ((derivedPullback U.ι).obj K) ≫
  (schemeDerivedDirectImage (pullback.fst g' U.ι ≫ f')).map
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' U.ι) U.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' U.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' U.ι)).map φ)

end AlgebraicGeometry
