/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineQCohComplexModel
import WeilConjectures.AlgebraicGeometry.AffineExtensionSectionsModelMate

/-! # Unit compatibility of affine extension and sections

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-extension-sections-unit).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The affine extension comparison respects the fixed adjunction units.
Only Q on Spec R must have quasi-coherent cohomology. No f, base-change square,
map m, or base-change morphism occurs in this statement.
Source: Stacks, perfect.tex, Tag 06Z0 and Tags 08DV, 08DW;
Tag 0AA7, extension/restriction adjunct construction.
(blueprint: lem-pc-affine-extension-sections-unit).
Proof:
1. Use the affine quasi-coherent derived equivalence to represent Q by a
complex of R-modules. Choose a K-flat resolution of this complex. Exact tilde
sends its quasi-isomorphism to a quasi-isomorphism, and its source is K-flat.
2. The derived tilde/pullback formula identifies Lg*Q with tilde of derived
extension of this module complex. Apply derived sections on Spec B and the
counit of the affine equivalence to obtain the required isomorphism.
3. On these resolutions, extension/restriction is adjoint to the underived
tensor pullback/direct image under tilde and sections. Their units agree.
Descend this adjunction through localization. Uniqueness of left adjoints to
the fixed derived restriction transports it to affineDerivedExtensionAdjunction.
4. The right-derived-unit equation hr identifies
its sections/direct-image comparison with the supplied r by right-derived
uniqueness. Thus the transported isomorphism satisfies the displayed equation.
The zero complex and identity ring map give the usual unit and impose no
extra assumptions; extension need not be exact or the map flat. -/
theorem exists_affineExtensionSectionsUnit
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
    (Q : schemeDerivedCategory (Spec R)) (hQ : schemeDerivedQCohProperty (Spec R) Q) :
    ∃ a : (affineDerivedExtension g).obj
        ((affineDerivedGlobalSections (𝟙 (Spec R))).obj Q) ≅
      (affineDerivedGlobalSections (𝟙 (Spec B))).obj ((derivedPullback g).obj Q),
      (affineDerivedExtensionAdjunction g).unit.app
          ((affineDerivedGlobalSections (𝟙 (Spec R))).obj Q) ≫
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.map a.hom =
      (affineDerivedGlobalSections (𝟙 (Spec R))).map
          ((canonicalPullbackAdjunction g).unit.app Q) ≫
        r.hom.app ((derivedPullback g).obj Q) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_affineQCohComplexModel Q hQ
  let ΓR := affineDerivedGlobalSections (𝟙 (Spec R))
  let ΓB := affineDerivedGlobalSections (𝟙 (Spec B))
  let L := derivedPullback g
  let E := affineDerivedExtension g
  let S := (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory
  let adj := affineDerivedExtensionAdjunction g
  let n (K : schemeDerivedCategory (Spec R)) :=
    (adj.homEquiv _ _).symm
      (ΓR.map ((canonicalPullbackAdjunction g).unit.app K) ≫ r.hom.app (L.obj K))
  have hn (K K' : schemeDerivedCategory (Spec R)) (f : K ⟶ K') :
      n K ≫ ΓB.map (L.map f) = E.map (ΓR.map f) ≫ n K' := by
    dsimp only [n]
    erw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
    congr 1
    have hunit := (canonicalPullbackAdjunction g).unit.naturality f
    have hrnat := r.hom.naturality (L.map f)
    dsimp only [Functor.comp_map, Functor.id_map] at hunit hrnat
    rw [Category.assoc]
    erw [← hrnat]
    rw [← Category.assoc]
    erw [← ΓR.map_comp]
    erw [← hunit]
    rw [ΓR.map_comp, Category.assoc]
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
      (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have hmodel : IsIso (n (DerivedCategory.Q.obj (T.obj M))) := by
    exact affineExtensionSections_model_mate_isIso g v r hr M hM
  have hniso : IsIso (n Q) := by
    have h := hn Q _ e.hom
    have he : IsIso (ΓB.map (L.map e.hom)) := by infer_instance
    have hright : IsIso (E.map (ΓR.map e.hom) ≫ n _) := by infer_instance
    have hcomp : IsIso (n Q ≫ ΓB.map (L.map e.hom)) := h ▸ hright
    exact IsIso.of_isIso_comp_right (n Q) (ΓB.map (L.map e.hom))
  refine ⟨asIso (n Q), ?_⟩
  change adj.unit.app (ΓR.obj Q) ≫ S.map (n Q) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

end AlgebraicGeometry
