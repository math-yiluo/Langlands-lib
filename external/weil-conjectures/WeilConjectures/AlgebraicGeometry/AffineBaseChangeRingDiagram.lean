/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The explicit ring diagram of an affine base change
Source: Stacks Project, Tag 09RE, affine calculation, and Tag 01JO.
(blueprint: def-pc-affine-base-change-ring-diagram). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- The indexing functor from the order-theoretic tail to the categorical under category.
Source: Stacks Project, Tag 09RE, affine calculation.
(blueprint: def-pc-affine-base-change-ring-diagram). -/
def affineBaseChangeTail {I : Type u} [Preorder I] (i : I) : Set.Ici i ⥤ Under i where
  obj j := Under.mk (homOfLE j.property)
  map {j k} f := Under.homMk (homOfLE (leOfHom f)) (by subsingleton)

/-- Push out the tail of R along the ring map representing t.hom followed by s.
Thus its value at j is the categorical realization of Gamma(Y) tensor over R(i) R(j).
This abbreviates Mathlib's generic Under.post / Under.pushout construction at the
order-theoretic tail and supplied structural map. No existence witness is used.
Source: Stacks Project, Tags 09RE and 01JO.
(blueprint: def-pc-affine-base-change-ring-diagram). -/
noncomputable def affineBaseChangeRingDiagram {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (i : I) (Y : Scheme.{u})
    (s : Y ⟶ Spec (R.obj i)) (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y) :
    Set.Ici i ⥤ CommRingCat.{u} :=
  affineBaseChangeTail i ⋙ Under.post R ⋙ Under.pushout (Spec.preimage (t.hom ≫ s)) ⋙
    Under.forget (Scheme.Γ.obj (.op Y))

/-- The initial structural map from the global-section ring into its base change.
Source: Stacks Project, Tags 09RE and 01JO.
(blueprint: def-pc-affine-base-change-ring-diagram). -/
noncomputable def affineBaseChangeInitialMap {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (i : I) (Y : Scheme.{u})
    (s : Y ⟶ Spec (R.obj i)) (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y) :
    Scheme.Γ.obj (.op Y) →+* (affineBaseChangeRingDiagram R i Y s t).obj ⟨i, le_rfl⟩ :=
  (((affineBaseChangeTail i ⋙ Under.post R ⋙
    Under.pushout (Spec.preimage (t.hom ≫ s))).obj ⟨i, le_rfl⟩).hom).hom

-- Keep the pushout construction from unfolding while elaborating its complex models.
attribute [irreducible] affineBaseChangeRingDiagram affineBaseChangeInitialMap

end AlgebraicGeometry
