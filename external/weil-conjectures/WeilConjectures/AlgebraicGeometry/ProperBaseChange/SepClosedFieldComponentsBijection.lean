/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Connected components after extension of a separably closed field

## References

* Stacks Project, Varieties, Tag 0363, first assertion
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Over a separably closed field, arbitrary field extension induces a bijection on connected
components of any scheme. The map sends the component of a point to the component of its image
under the first projection. No finiteness or nonemptiness assumption is needed. -/
theorem bijective_connectedComponentsMap_pullback_fst_of_isSepClosed
    (k L : Type u) [Field k] [IsSepClosed k] [Field L] [Algebra k L]
    (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))] :
    Function.Bijective
      (pullback.fst (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).continuous.connectedComponentsMap := by
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed _
  let p := pullback.fst (Z ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let e := p.connectedComponentsHomeomorph p.isOpenMap
  have he : e = p.continuous.connectedComponentsMap := by
    funext c
    exact Scheme.Hom.connectedComponentsHomeomorph_apply p p.isOpenMap c
  rw [← he]
  exact e.bijective

end AlgebraicGeometry
