/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnderivedModel
import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsModelFactorization

/-! # Invertibility of the affine unit mate on K-flat tilde models

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: lem-pc-affine-extension-sections-model-mate).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The normalized extension/sections mate is invertible on termwise tilde models.
Source: Stacks, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: lem-pc-affine-extension-sections-model-mate).
Proof: The given complex M is K-flat. Exact tilde carries M to a K-flat
complex. The affine pullback formula identifies pulled-back tilde M with
tilde of B tensor M.
Derived sections recovers the latter module complex by the affine equivalence.
The extension/restriction adjunction on complexes identifies the transpose of
the pullback unit with this comparison. Localization preserves this equation;
uniqueness of left adjoints identifies the fixed extension adjunction. The
equation hr identifies the derived lift of the underived sections comparison v
with r by the right-derived universal property. Thus the
transpose in the statement is a composite of comparison isomorphisms. Neither
flatness of the ring map nor boundedness of M is used. -/
theorem affineExtensionSections_model_mate_isIso
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let Q := DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} R ⥤
              SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
              (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    IsIso (((affineDerivedExtensionAdjunction g).homEquiv _ _).symm
      ((affineDerivedGlobalSections (𝟙 (Spec R))).map
          ((canonicalPullbackAdjunction g).unit.app Q) ≫
        r.hom.app ((derivedPullback g).obj Q))) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  have hT : (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := R) f g
  have hE : (ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).left_adjoint_additive
  have hP : (@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)).Additive :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).left_adjoint_additive
  obtain ⟨c, hc⟩ := exists_affineExtensionSections_underived_model g v
  obtain ⟨a, b, hab⟩ := @exists_affineExtensionSections_model_factorization _ _ R B g v r hr
    c.hom hc hT hE hP M hM
  have : IsIso ((c.hom.mapHomologicalComplex (.up ℤ)).app M) := by
    change IsIso (((NatIso.mapHomologicalComplex c (.up ℤ)).app M).hom)
    infer_instance
  have : IsIso (DerivedCategory.Q.map ((c.hom.mapHomologicalComplex (.up ℤ)).app M)) := by
    infer_instance
  exact IsIso.of_isIso_fac_right hab

end AlgebraicGeometry
