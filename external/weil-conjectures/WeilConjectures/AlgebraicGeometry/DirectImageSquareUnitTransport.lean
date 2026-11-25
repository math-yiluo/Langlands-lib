/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Equality transport of the ordinary direct-image square
Source: Stacks Project, Tags 08HY and 0D5T.
(blueprint: lem-pc-direct-image-square-unit-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The ordinary comparison, constructed from pushforward composition and equality transport.
Source: Stacks, Tags 08HY and 0D5T.
(blueprint: lem-pc-direct-image-square-unit-transport). -/
@[irreducible] noncomputable def directImageSquareIso {A B C D : Scheme.{u}}
    (s : A ⟶ B) (t : B ⟶ D) (q : A ⟶ C) (r : C ⟶ D) (h : s ≫ t = q ≫ r) :
    RingedSpace.moduleDirectImage s.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage t.toLRSHom.toShHom ≅
      RingedSpace.moduleDirectImage q.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage r.toLRSHom.toShHom :=
  Scheme.Modules.pushforwardComp s t ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp q r).symm


set_option backward.isDefEq.respectTransparency false in
/-- The constructed comparison is the identity on whole-space sections.
Source: Stacks, Tags 08HY and 0D5T.
(blueprint: lem-pc-direct-image-square-unit-transport). -/
theorem directImageSquareIso_top {A B C D : Scheme.{u}}
    (s : A ⟶ B) (t : B ⟶ D) (q : A ⟶ C) (r : C ⟶ D) (h : s ≫ t = q ≫ r)
    (M : SheafOfModules.{u} (moduleRings A.toRingedSpace)) (x : M.val.obj (op ⊤)) :
    (((directImageSquareIso s t q r h).hom.app M).val.app (op ⊤)) x = x := by
  simp only [directImageSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  change (((Scheme.Modules.pushforwardComp s t).hom.app M).val.app (op ⊤) ≫
    ((Scheme.Modules.pushforwardCongr h).hom.app M).val.app (op ⊤) ≫
    ((Scheme.Modules.pushforwardComp q r).inv.app M).val.app (op ⊤)) x = x
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.pushforwardComp]
  change ((Scheme.Modules.pushforwardCongr h).hom.app M).app ⊤ x = x
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  change M.val.presheaf.map (𝟙 (op ⊤)) x = x
  simp


section EqualityTransport
-- Keep the localization and its chosen right-derived units folded during comparison.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pushforwardCongr_eq {A D : Scheme.{u}}
    (v v' : A ⟶ D) (h : v = v') :
    (Scheme.Modules.pushforwardCongr h).hom =
      eqToHom (congrArg
        (fun f : A ⟶ D ↦ RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h) := by
  subst v'
  ext M U
  simp
  rfl



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directImage_unit_congr {A D : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.toRingedSpace))]
    (v v' : A ⟶ D) (h : v = v')
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (eqToHom (congrArg (fun f : A ⟶ D ↦ schemeDerivedDirectImage.{u, w} f) h)).app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (eqToHom (congrArg
            (fun f : A ⟶ D ↦ RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h))
            (.up ℤ)).app K) ≫
        (RingedSpace.moduleDirectImage v'.toLRSHom.toShHom).rightDerivedFunctorUnit.app K := by
  subst v'
  simp

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
-- Matching the composite homotopy functors unfolds the sheaf scalar restrictions.
/-- Equality transport of a single right-derived unit across the ordinary square.
Source: Stacks Project, Tags 08HY and 0D5T.
(blueprint: lem-pc-direct-image-square-unit-transport).
Proof: moduleDirectImage of a composite is definitionally the composite
of the two moduleDirectImage functors. The pushforwardComp hom and inv are
identities on sections over every open (not just the whole space), by the
Mathlib component formulas. Consequently these comparison maps identify
with the equality maps for the definitionally equal functors. On complexes
they are degreewise identities; on homotopy objects this follows by taking
a representative under HomotopyCategory.quotient and using that the quotient
functor maps identity maps to identities.
After these identifications the ordinary square comparison is equality
transport along h. For a single scheme morphism v, its chosen derived
functor and its unit form a family in v. Naturality of a family of morphisms
under equality (eqToHom_naturality, or induction on that equality) says that
its unit followed by the equality map of the derived functors equals the
equality map of the source functors followed by its unit. Additivity is a
proposition, so the additive instance introduces no extra comparison.
Applying Qh to the homotopy equality map gives precisely the source equality
map in that naturality equation: functors preserve eqToHom. Substituting the
ordinary comparison just identified proves the displayed equation.
Only equality maps are simplified; no unit is cancelled. The argument works
for arbitrary homotopy complexes, zero complexes, identity squares, and
empty schemes, with no acyclicity hypothesis. -/
theorem directImageSquare_unit_transport {A B C D : Scheme.{u}}
    (s : A ⟶ B) (t : B ⟶ D) (q : A ⟶ C) (r : C ⟶ D) (h : s ≫ t = q ≫ r)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (eqToHom (congrArg (fun v ↦ schemeDerivedDirectImage.{u, w} v) h)).app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          (((directImageSquareIso s t q r h).hom.mapHomotopyCategory (.up ℤ)).app K) ≫
        (RingedSpace.moduleDirectImage (q ≫ r).toLRSHom.toShHom).rightDerivedFunctorUnit.app K
    := by
  simp only [directImageSquareIso, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.pushforwardComp, SheafOfModules.pushforwardComp,
    Iso.refl_hom, Iso.refl_inv]
  rw [pushforwardCongr_eq]
  exact directImage_unit_congr (s ≫ t) (q ≫ r) h K

end EqualityTransport

end AlgebraicGeometry
