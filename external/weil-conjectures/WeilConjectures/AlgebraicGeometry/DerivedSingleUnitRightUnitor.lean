/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-!
# Functorial normalization of the single-unit comparison

Source: the normalized projective counit calculation in
`lem-amb-affine-space-top-trace.proof.md`.
(blueprint: lem-route-derived-single-unit-right-unitor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w z
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Postcomposing the image of the canonical single-unit comparison changes no map.
Source: the projective-line counit identification in the first paragraph of
`lem-amb-affine-space-top-trace.proof.md`.
(blueprint: lem-route-derived-single-unit-right-unitor)

Proof: the canonical single-unit isomorphism has identity inverse, hence identity
forward map by its hom-inv identity. A functor sends this identity to the identity,
and postcomposition cancels it by the category left-identity law.
In particular this cancels the single-unit factor before the derived right unitor.
The argument works on the empty scheme and over the zero coefficient ring.
-/
theorem map_singleFunctorObjUnitIso_hom_comp
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) {D : Type w} [Category.{z} D]
    (F : DerivedCategory (Sheaf T.smallEtaleTopology B) ⥤ D) {Y : D}
    (g : F.obj (𝟙_ (DerivedCategory (Sheaf T.smallEtaleTopology B))) ⟶ Y) :
    F.map (singleFunctorObjUnitIso B T).hom ≫ g = cast (by rfl) g := by
  simp only [cast_eq]
  have hu : (singleFunctorObjUnitIso B T).hom = 𝟙 _ := by
    have h := (singleFunctorObjUnitIso B T).hom_inv_id
    rwa [singleFunctorObjUnitIso_inv, Category.comp_id] at h
  rw [hu, CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale
