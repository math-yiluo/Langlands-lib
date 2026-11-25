/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf

/-! # From an étale local isomorphism to a geometric stalk section

## References

* Stacks Project, Tag 09BV
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A representative of the local Isom presheaf over an étale neighbourhood of a
geometric point gives an element of the sheafified Isom stalk.  This isolates the
sheafification and point-fibre step from finite-level comparison.
-/
theorem lisse_finite_level_etale_stalk_from_local_section
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (V : X.Etale) (v : (pointSmallEtale x).fiber.obj V)
    (h : Nonempty ((localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj D)) :
    Nonempty ((pointSmallEtale x).sheafFiber.obj
      (derivedLocalIsomorphismSheaf A D)) := by
  rcases h with ⟨e⟩
  let P := derivedLocalIsomorphismPresheaf A D
  let η := CategoryTheory.toSheafify X.smallEtaleTopology P
  refine ⟨((pointSmallEtale x).presheafFiber.map η)
    ((pointSmallEtale x).toPresheafFiber V v P e)⟩

end AlgebraicGeometry.Scheme
