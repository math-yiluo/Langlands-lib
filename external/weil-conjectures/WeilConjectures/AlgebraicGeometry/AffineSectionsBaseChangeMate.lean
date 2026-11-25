/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSectionsCompositionComparisons
import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsUnit
import WeilConjectures.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare
import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Affine sections and the mate of sheaf base change

Source: Stacks Project, perfect.tex, Tag 0AA7; cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-pc-affine-sections-base-change-mate).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine sections comparison intertwines the extension/restriction mate with
sheaf base change, followed by the pullback/direct-image mate of any morphism.
The supplied sections comparison is normalized on sheaves and right-derived units.
Only the pushforward of E is required to have quasi-coherent cohomology; neither
Tor independence nor invertibility of the morphism or of base change is required.

Source: Stacks Project, perfect.tex, Tag 0AA7, construction of the canonical map;
cohomology.tex, Tag 08HY, counit description of base change, and Tag 0D5T.
(blueprint: lem-pc-affine-sections-base-change-mate).

Proof:
1. Derived direct-image composition and exact scalar restriction give a natural
   isomorphism Rf'_* followed by RΓ over B with RΓ over f'. On sheaves it is the
   identity on sections, and the composition of right-derived units specifies its
   derived normalization. The same construction over R identifies RΓ over f with
   RΓ over Spec R after Rf_*.
2. For Q = Rf_*E, use the affine quasi-coherent derived equivalence on Spec R
   and Spec B. Resolve its module model by a K-flat complex. The tilde/pullback
   formula identifies Lg*Q with tilde of extension of scalars. The extension and
   restriction adjunction on these complexes descends to localization. Compare
   the descended adjunction with the fixed affineDerivedExtensionAdjunction by
   uniqueness of left adjoints to the fixed derived restriction functor. This
   yields the source isomorphism a commuting with the adjunction units. Compose
   with extension of the inverse sections/pushforward isomorphism of step 1.
3. Transpose the displayed right-hand composite under affine extension/restriction.
   By the unit compatibility of a this is RΓ of the unit for Lg*, followed by
   restriction of the sections of sheaf base change and of the mate of m.
   Expand base change as the mate of pullback composition and the counit for f.
   Naturality moves m past the counit; the triangle identities cancel the unit
   and counit pairs. Direct-image composition identifies what remains with RΓ(m)
   followed by the sections comparison for g_X. On K-injective models both
   sections comparisons act as the identity on sections. The supplied underived
   identity and right-derived-unit equation therefore identify this comparison
   with c. Equality on all objects follows by the right-derived universal property.
4. Apply injectivity of the affine adjunction Hom equivalence. The construction
   of a and the target sections isomorphism does not depend on L or m, giving
   the stated simultaneous equality. -/
theorem exists_affineSectionsBaseChangeMate
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty (Spec R) ((schemeDerivedDirectImage f).obj E))
    (s : RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom ⋙
        affineGlobalSections f ≅
      affineGlobalSections (pullback.snd f g) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (c : schemeDerivedDirectImage (pullback.fst f g) ⋙
        affineDerivedGlobalSections f ≅
      affineDerivedGlobalSections (pullback.snd f g) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hs : ∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (affineGlobalSections (pullback.snd f g)).obj F),
      (s.hom.app F) x = x)
    (hc : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom)
          (affineGlobalSections f)).app J ≫
        (affineGlobalSectionsDerivedIso f).hom.app
          ((schemeDerivedDirectImage (pullback.fst f g)).obj (DerivedCategory.Qh.obj J)) ≫
        c.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (pullback.snd f g) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (affineBaseChangedSectionsDerivedIso f g).hom.app (DerivedCategory.Qh.obj J)) :
    ∃ a : (affineDerivedExtension g).obj ((affineDerivedGlobalSections f).obj E) ≅
        (affineDerivedGlobalSections (𝟙 (Spec B))).obj
          ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)),
      ∃ d : schemeDerivedDirectImage (pullback.snd f g) ⋙
          affineDerivedGlobalSections (𝟙 (Spec B)) ≅
          affineDerivedGlobalSections (pullback.snd f g),
        ∀ (L : schemeDerivedCategory (pullback f g))
          (m : E ⟶ (schemeDerivedDirectImage (pullback.fst f g)).obj L),
          ((affineDerivedExtensionAdjunction g).homEquiv _ _).symm
              ((affineDerivedGlobalSections f).map m ≫ c.hom.app L) =
            a.hom ≫ (affineDerivedGlobalSections (𝟙 (Spec B))).map
              (schemeDerivedBaseChangeMap f (pullback.snd f g) g
                (pullback.fst f g) pullback.condition E) ≫
              (affineDerivedGlobalSections (𝟙 (Spec B))).map
                ((schemeDerivedDirectImage (pullback.snd f g)).map
                  (((canonicalPullbackAdjunction (pullback.fst f g)).homEquiv E L).symm m)) ≫
              d.hom.app L := by
  obtain ⟨t, b, z, d, v, r, ht, hb, hz, hd, hv, hr⟩ :=
    exists_affineSectionsCompositionComparisons f g
  obtain ⟨a₀, ha₀⟩ := exists_affineExtensionSectionsUnit g v r hr
    ((schemeDerivedDirectImage f).obj E) hE
  let a := (affineDerivedExtension g).mapIso (b.app E).symm ≪≫ a₀
  have ha : (affineDerivedExtensionAdjunction g).unit.app
        ((affineDerivedGlobalSections f).obj E) ≫
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.map a.hom =
    b.inv.app E ≫ (affineDerivedGlobalSections (𝟙 (Spec R))).map
        ((canonicalPullbackAdjunction g).unit.app ((schemeDerivedDirectImage f).obj E)) ≫
      r.hom.app ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) := by
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
    rw [Functor.map_comp, ← Category.assoc]
    erw [← (affineDerivedExtensionAdjunction g).unit.naturality (b.inv.app E)]
    simp only [Functor.id_map, Functor.comp_obj]
    erw [Category.assoc, ha₀]
  have hu := affineSectionsBaseChange_unit_square f g t b ht hb z d hz hd
    v r hv hr E s c hs hc
  refine ⟨a, d, ?_⟩
  intro L m
  let n := ((canonicalPullbackAdjunction (pullback.fst f g)).homEquiv E L).symm m
  have hm : (canonicalPullbackAdjunction (pullback.fst f g)).unit.app E ≫
      (schemeDerivedDirectImage (pullback.fst f g)).map n = m := by
    exact ((canonicalPullbackAdjunction (pullback.fst f g)).homEquiv E L).apply_symm_apply m
  apply ((affineDerivedExtensionAdjunction g).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc, ha]
  let S := (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory
  have hn := d.hom.naturality n
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [← S.map_comp, hn, S.map_comp]
  have hu' := congrArg (fun k ↦ b.inv.app E ≫ k) hu
  simp only [Functor.map_comp, Iso.inv_hom_id_app_assoc] at hu'
  erw [reassoc_of% hu']
  erw [← c.hom.naturality n]
  change (affineDerivedGlobalSections f).map m ≫ c.hom.app L =
    (affineDerivedGlobalSections f).map
        ((canonicalPullbackAdjunction (pullback.fst f g)).unit.app E) ≫
      (affineDerivedGlobalSections f).map
        ((schemeDerivedDirectImage (pullback.fst f g)).map n) ≫ c.hom.app L
  rw [← Category.assoc, ← Functor.map_comp, hm]

end AlgebraicGeometry
