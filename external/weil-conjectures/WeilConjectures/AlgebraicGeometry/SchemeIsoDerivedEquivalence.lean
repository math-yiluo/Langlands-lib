/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Derived transport along an isomorphism of schemes

Source: Stacks Project, perfect.tex, Tag 08EB, affine isomorphism transport
(blueprint: lem-pc-scheme-iso-derived-equivalence).
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Functor

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Modules.pushforwardComp s.hom s.inv ≪≫
      Modules.pushforwardCongr s.hom_inv_id ≪≫ Modules.pushforwardId X).symm)
    (Modules.pushforwardComp s.inv s.hom ≪≫
      Modules.pushforwardCongr s.inv_hom_id ≪≫ Modules.pushforwardId Y)

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along a scheme isomorphism induces an equivalence on any chosen derived
categories, compatible with localization of its explicit termwise pushforward.
Source: Stacks Project, perfect.tex, Tag 08EB, affine isomorphism transport
(blueprint: lem-pc-scheme-iso-derived-equivalence).

Proof: Pushforwards along the isomorphism and its inverse form an equivalence: compose the
pushforward composition comparison, the equality of the composite with the identity, and
pushforward of the identity. Equivalences of abelian categories are additive and exact.
The termwise functors therefore preserve quasi-isomorphisms. Localize both functors and
localize their unit and counit to obtain inverse derived functors. The localization
factorization is the asserted comparison. This works for independent morphism universes. -/
theorem exists_scheme_iso_derived_equivalence {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ e : schemeDerivedCategory X ≌ schemeDerivedCategory Y,
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (@Functor.mapHomologicalComplex ℤ
          (SheafOfModules.{u} (moduleRings X.toRingedSpace))
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
          (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
          ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) := by
  let e₀ := moduleIsoEquivalence s
  let F := e₀.functor
  let G := e₀.inverse
  have : F.IsEquivalence := e₀.isEquivalence_functor
  have : G.IsEquivalence := e₀.isEquivalence_inverse
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let eC := e₀.mapHomologicalComplex (ComplexShape.up ℤ)
  let α : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eC.unitIso.symm _ ≪≫
      Functor.leftUnitor _
  let β : (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      F.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eC.counitIso _ ≪≫
      Functor.leftUnitor _
  let e := Localization.equivalence DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory
    (G.mapHomologicalComplex _ ⋙ DerivedCategory.Q) G.mapDerivedCategory α β
  exact ⟨e, ⟨F.mapDerivedCategoryFactors⟩⟩

end AlgebraicGeometry.Scheme
