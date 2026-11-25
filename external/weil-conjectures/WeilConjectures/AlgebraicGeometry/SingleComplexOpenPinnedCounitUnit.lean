/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction

/-! # Shared normalization of the pinned derived counit

Source: Stacks Project, Tag 08HY.
The calculation is shared by open counit compatibility and unit-square normalization.
(blueprint: lem-pc-open-pinned-counit-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem counit_factorization
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₁} {L : D₁ ⥤ D₂} {R : D₂ ⥤ D₁}
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (b : G ⊣ H) (a : L ⊣ R)
    (ε : Q₁ ⋙ L ⟶ G ⋙ Q₂) (η : H ⋙ Q₁ ⟶ Q₂ ⋙ R)
    (h : ∀ (M : C₁) (K : C₂) (v : G.obj M ⟶ K),
      a.homEquiv (Q₁.obj M) (Q₂.obj K) (ε.app M ≫ Q₂.map v) =
        Q₁.map (b.homEquiv M K v) ≫ η.app K) (I : C₂) :
    L.map (η.app I) ≫ a.counit.app (Q₂.obj I) =
      ε.app (H.obj I) ≫ Q₂.map (b.counit.app I) := by
  apply (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).injective
  have h₁ := (a.homEquiv (Q₁.obj (H.obj I)) (Q₂.obj I)).apply_symm_apply (η.app I)
  have h₂ := (b.homEquiv (H.obj I) I).apply_symm_apply (𝟙 (H.obj I))
  simp only [a.homEquiv_counit] at h₁
  simp only [b.homEquiv_symm_id] at h₂
  rw [h₁, h, h₂, Q₁.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalize the pinned derived counit at a homotopy representative.
Source: Stacks Project, Tag 08HY, and `exists_schemeDerivedAdjunction`.
(blueprint: lem-pc-open-pinned-counit-unit).

Proof: Apply the compatibility of the pinned Hom equivalence to the underived
homotopy counit. Its image under the underived adjunction is the identity.
The image under localization is therefore the right-derived unit. Injectivity
of the derived Hom equivalence identifies its inverse image, pullback of that
unit followed by the derived counit, with the left-derived counit followed by
the localized underived counit. This calculation applies to every homotopy
complex; it uses neither invertibility of the unit nor K-injectivity. -/
theorem singleComplexOpen_pinned_counit_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) f
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback f).map (F.rightDerivedFunctorUnit.app I) ≫
        (a f).counit.app (DerivedCategory.Qh.obj I) =
      (ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
            |>.mapHomotopyCategory (.up ℤ)).counit.app I) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : (Scheme.Modules.tensorPullback f).Additive :=
    (Classical.choose exists_derivedPullbackComposition) f
  exact counit_factorization
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      |>.mapHomotopyCategory (.up ℤ))
    (singleComplexOpenPinnedAdjunction f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
    (Classical.choose_spec (exists_schemeDerivedAdjunction f
      (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f))) I

end AlgebraicGeometry
