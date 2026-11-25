/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.LocalizedOpenSheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Tensor comparison for the localized open-site equivalence

Source: Stacks Project, Modules, Tag 01CD.
(blueprint: lem-sc-localized-open-tensor-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The equivalence from the localized open site to the open subscheme preserves
sheaf tensor products, naturally in both factors.
Source: Stacks Project, Modules, Tag 01CD, applied to the equivalence of open sites.
(blueprint: lem-sc-localized-open-tensor-equivalence).

Proof: an object of the localized site is an open V contained in U, and corresponds
under the open-site equivalence to the same open V of U.toScheme. The coefficient
rings identify by the restriction isomorphism of the structure sheaf. On presheaf
modules the tensor comparison sends a pure tensor of sections to the tensor of the
corresponding sections; its inverse uses the inverse coefficient isomorphism.
The balanced relations and restriction maps are preserved. The site equivalence
preserves covering sieves, so these inverse maps descend through sheafification
to inverse maps of sheaf tensors. Applying either module map to a pure tensor
commutes with this construction, which gives the displayed naturality identity.
The construction also applies to the empty open and to zero modules. -/
theorem exists_localizedOpen_tensor_equivalence (X : Scheme.{u}) (U : X.Opens) :
    letI : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
      SheafOfModules.monoidalCategory (X.sheaf.over U)
    let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    ∃ e : ∀ (F G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)),
      E.obj (F ⊗ G) ≅ E.obj F ⊗ E.obj G,
      ∀ (F F' G G' : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (f : F ⟶ F') (g : G ⟶ G'),
        E.map (f ⊗ₘ g) ≫ (e F' G').hom =
          (e F G).hom ≫ (E.map f ⊗ₘ E.map g) := by
  let : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let : MonoidalCategory
      (PresheafOfModules.{u} ((moduleRings X.toRingedSpace).over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let : MonoidalCategory
      (PresheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace).obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.sheaf.obj)
  let L := PresheafOfModules.sheafification.{u}
    (R := (moduleRings X.toRingedSpace).over U)
    (𝟙 ((moduleRings X.toRingedSpace).over U).obj)
  let P := PresheafOfModules.pushforward₀OfCommRingCat
    (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj
  let S := PresheafOfModules.sheafification.{u}
    (R₀ := (moduleRings U.toScheme.toRingedSpace).obj)
    (R := moduleRings U.toScheme.toRingedSpace)
    (𝟙 (moduleRings U.toScheme.toRingedSpace).obj)
  let W := ((Opens.grothendieckTopology X).over U).W.inverseImage
    (PresheafOfModules.toPresheaf.{u} ((moduleRings X.toRingedSpace).over U).obj)
  let : L.Monoidal := SheafOfModules.sheafificationMonoidal (X.sheaf.over U)
  let : S.Monoidal := SheafOfModules.sheafificationMonoidal U.toScheme.sheaf
  let : P.Monoidal := inferInstanceAs
    (PresheafOfModules.pushforward₀OfCommRingCat
      (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj).Monoidal
  let : (P ⋙ S).Monoidal := Functor.Monoidal.instComp P S
  obtain ⟨h⟩ := exists_localizedOpen_sheafification_iso X U
  let : Localization.Lifting L W (P ⋙ S) E := ⟨h⟩
  let : E.Monoidal := Localization.Monoidal.functorMonoidalOfComp L W E (P ⋙ S)
  refine ⟨fun F G ↦ (Functor.Monoidal.μIso E F G).symm, ?_⟩
  intro F F' G G' f g
  exact (Functor.OplaxMonoidal.δ_natural E f g).symm

end AlgebraicGeometry
