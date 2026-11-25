/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The derived restriction square of a scheme isomorphism

Source: Stacks Project, Tag 09IR, isomorphism transport in the affine setup;
Mathlib scheme-module restriction composition and localization uniqueness.
(blueprint: lem-pc-scheme-iso-derived-restriction-square).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {S T : Scheme.{u}} (s : S ≅ T) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings T.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Modules.pushforwardComp s.hom s.inv ≪≫
      Modules.pushforwardCongr s.hom_inv_id ≪≫ Modules.pushforwardId S).symm)
    (Modules.pushforwardComp s.inv s.hom ≪≫
      Modules.pushforwardCongr s.inv_hom_id ≪≫ Modules.pushforwardId T)

set_option backward.isDefEq.respectTransparency false in
/-- The derived equivalence on corresponding open sites commutes with restriction.
Source: Stacks Project, Tag 09IR; restriction-comparison part of step 1 of
lem-pc-affine-derived-open-transport.
(blueprint: lem-pc-scheme-iso-derived-restriction-square).

Proof: Restrict s to the isomorphism s.hom.preimageIso U between the open subschemes.
Pushforward along this isomorphism and its inverse gives an exact equivalence on
module sheaves. Compose with Modules.overEquiv on each side to obtain an exact
module-sheaf equivalence on the two localized open sites. Apply its termwise
complex functor and localize to obtain the displayed equivalence eU.
The global module-sheaf pushforward along s is isomorphic to restriction along
s.inv, since both are left adjoint to pushforward along s.inv. Similarly identify
the open isomorphism pushforward with restriction along its inverse. Compose
Modules.overFunctorEquiv, restrictFunctorComp and restrictFunctorCongr with the
identity s.hom.preimageIso_hom_ι (or its inverse version). These identify the two
composites of underived functors, by restriction to the same opens with the same
structure-ring maps. Their termwise natural comparison descends by localization.
The given he identifies e.functor with the derived isomorphism pushforward by
uniqueness of localization. Composing this comparison with the localized module
restriction comparison yields the displayed square. The argument needs no
quasi-coherence, perfection or nonempty points and includes empty and full U. -/
theorem exists_scheme_iso_derived_restriction_square {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (U : Y.Opens) :
    ∃ eU : DerivedCategory (SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (s.hom ⁻¹ᵁ U))) ≌
      DerivedCategory (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)),
      Nonempty (e.functor ⋙ (SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) (s.hom ⁻¹ᵁ U)).mapDerivedCategory ⋙ eU.functor) := by
  let V := s.hom ⁻¹ᵁ U
  let i := s.hom.preimageIso U
  let e₀ := moduleIsoEquivalence s
  let eI := moduleIsoEquivalence i
  let EV := Modules.overEquiv V
  let EU := Modules.overEquiv U
  let eO := (EV.trans eI).trans EU.symm
  have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eI.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eO.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_full eO.functor
  have : eO.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eO.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let LX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let LY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let cG : e₀.functor ≅ Modules.restrictFunctor s.inv :=
    Adjunction.leftAdjointUniq e₀.toAdjunction (Modules.restrictAdjunction s.inv)
  let cI : eI.functor ≅ Modules.restrictFunctor i.inv :=
    Adjunction.leftAdjointUniq eI.toAdjunction (Modules.restrictAdjunction i.inv)
  have fac : U.ι ≫ s.inv = i.inv ≫ V.ι := by
    apply (cancel_mono s.hom).mp
    simp only [Category.assoc, s.inv_hom_id, Category.comp_id]
    exact (Scheme.Hom.preimageIso_inv_ι s.hom U).symm
  let h0 : (e₀.functor ⋙ LY) ⋙ EU.functor ≅ (LX ⋙ EV.functor) ⋙ eI.functor :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (Modules.overFunctorEquiv U) ≪≫
      isoWhiskerRight cG _ ≪≫
      (Modules.restrictFunctorComp U.ι s.inv).symm ≪≫
      Modules.restrictFunctorCongr fac ≪≫
      Modules.restrictFunctorComp i.inv V.ι ≪≫
      isoWhiskerRight (Modules.overFunctorEquiv V).symm _ ≪≫
      isoWhiskerLeft _ cI.symm
  let h1 : e₀.functor ⋙ LY ≅ LX ⋙ eO.functor :=
    (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ EU.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight h0 EU.inverse ≪≫
      isoWhiskerRight (Functor.associator _ _ _) _ ≪≫ Functor.associator _ _ _
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      e.functor := ⟨he⟩
  let beta : e.functor ≅ e₀.functor.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (e₀.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      e.functor e₀.functor.mapDerivedCategory (Iso.refl _)
  let d := eO.mapDerivedCategory
  refine ⟨d, ⟨?_⟩⟩
  exact isoWhiskerRight beta LY.mapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso e₀.functor LY) ≪≫
    Functor.mapDerivedCategoryNatIso h1 ≪≫ (Functor.mapDerivedCategoryCompIso LX eO.functor).symm

end AlgebraicGeometry.Scheme
