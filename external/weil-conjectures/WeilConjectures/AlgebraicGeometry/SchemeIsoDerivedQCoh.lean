/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-! # Quasi-coherent cohomology under a scheme isomorphism

Source: Stacks Project, Tag 08EB, and exact isomorphism pushforward
(blueprint: lem-pc-scheme-iso-derived-qcoh).
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory CategoryTheory.Limits Functor

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
/-- The inverse of an isomorphism-induced derived equivalence preserves quasi-coherent
cohomology. Source: Stacks Project, Tag 08EB, affine isomorphism transport.
(blueprint: lem-pc-scheme-iso-derived-qcoh).

Proof: Represent the inverse image by a complex P. The localization comparison and
counit identify E with the localization of s_* P. Exactness of isomorphism pushforward
identifies its homology with s_* H(P). These sheaves are quasi-coherent since E is.
Apply pushforward along the inverse isomorphism, which preserves quasi-coherence by the
affine pushforward theorem. Its composite with s_* is the identity, so H(P) is
quasi-coherent. The homology comparison for Q(P) gives the assertion in every degree. -/
theorem scheme_iso_derived_inverse_preserves_qcoh {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (E : schemeDerivedQCohCategory Y) :
    schemeDerivedQCohProperty X (e.inverse.obj E.obj) := by
  let e₀ := moduleIsoEquivalence s
  let F := e₀.functor
  let G := e₀.inverse
  have : F.IsEquivalence := e₀.isEquivalence_functor
  have : G.IsEquivalence := e₀.isEquivalence_inverse
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let P := DerivedCategory.Q.objPreimage (e.inverse.obj E.obj)
  let hP := DerivedCategory.Q.objObjPreimageIso (e.inverse.obj E.obj)
  let hFP : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ≅ E.obj :=
    (he.app P).symm ≪≫ e.functor.mapIso hP ≪≫ e.counitIso.app E.obj
  intro n
  let H := (HomologicalComplex.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) n).obj P
  let c : F.obj H ≅ (DerivedCategory.homologyFunctor _ n).obj E.obj :=
    ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).app P).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).symm.app _ ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso hFP
  have hF : (F.obj H).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso c.symm
      (E.property n)
  have hG : (G.obj (F.obj H)).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_isAffineHom s.inv (F.obj H)
  have hH : H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (e₀.unitIso.app H).symm hG
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors _ n).symm.app P ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso hP) hH

end AlgebraicGeometry.Scheme
