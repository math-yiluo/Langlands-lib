/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.AffineSectionsSquareMatePathUnit
import all WeilConjectures.AlgebraicGeometry.AffineSectionsPushforwardNormalization
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic

/-! # Coherence of normalized affine sections comparisons

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-sections-square-comparison-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

-- The exposed derived-scalar construction increases signature elaboration work.
/-- Normalized sections comparisons commute with the right-adjoint comparison of
an arbitrary fibre-product object. This assertion has no pullback units and no
base-change map: it only compares two ways to take sections of a composed direct image.
Source: Stacks, cohomology.tex, Tags 0D5T and 08HY; perfect.tex, Tag 0AA7.
(blueprint: lem-pc-affine-sections-square-comparison-coherence).
Proof: Choose a K-injective representative J of F. The composite direct-image units
are invertible on J: direct image sends such representatives to complexes acyclic
for the subsequent direct image and global sections (Tag 0D5T). Transpose the pinned
left-derived composition comparisons under their normalized adjunctions. The pinned
Hom-equivalence equation identifies the resulting right-adjoint comparison δ with
the right-derived comparison induced by pushforward composition and the commutative
square. Precompose the claimed equality with the pasted right-derived unit of the
composite p_*; f_*; Γ_R at J. Replace b and c using hb and hc, and replace r and d
using hr and hd. Naturality of each right-derived unit moves these units past the
underived comparison maps. The two resulting underived maps are identical: t, z, v
and s are identity on the underlying sections by ht, hz, hv and hs, and pullback.condition
identifies their R-actions. Cancel the invertible pasted unit at J. Finally every
object F is isomorphic to the localization of a K-injective representative; naturality
of all comparisons transports the equality from that representative to F. This
argument uses neither quasi-coherence nor invertibility of a base-change morphism.
For F=0 both maps are zero, and for identity squares it is the composition unit law. -/
theorem affineSections_square_comparison_coherence
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    (t : RingedSpace.moduleDirectImage (f).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅ affineGlobalSections (f))
    (b : schemeDerivedDirectImage (f) ⋙
        affineDerivedGlobalSections (𝟙 (Spec R)) ≅ affineDerivedGlobalSections (f))
    (ht : ∀ (M : SheafOfModules.{u} (moduleRings (X).toRingedSpace))
        (x : (affineGlobalSections (f)).obj M), (t.hom.app M) x = x)
    (hb : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (X).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (f).toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage (f)).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (f)).rightDerivedFunctorUnit.app J ≫
        (affineGlobalSectionsDerivedIso (f)).hom.app (DerivedCategory.Qh.obj J))
    (z : RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec B)) ≅ affineGlobalSections (pullback.snd f g))
    (d : schemeDerivedDirectImage (pullback.snd f g) ⋙
        affineDerivedGlobalSections (𝟙 (Spec B)) ≅ affineDerivedGlobalSections (pullback.snd f g))
    (hz : ∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (affineGlobalSections (pullback.snd f g)).obj M), (z.hom.app M) x = x)
    (hd : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom)
        (affineGlobalSections (𝟙 (Spec B)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec B))).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
        ((z.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (pullback.snd f g)).rightDerivedFunctorUnit.app J ≫
        (affineGlobalSectionsDerivedIso (pullback.snd f g)).hom.app (DerivedCategory.Qh.obj J))
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hv : ∀ (M : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (x : (affineGlobalSections (𝟙 (Spec B))).obj M), (v.hom.app M) x = x)
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
        (affineBaseChangedSectionsDerivedIso f g).hom.app (DerivedCategory.Qh.obj J))
    (F : schemeDerivedCategory (pullback f g)) :
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h) (pullback.condition (f := f) (g := g)).symm) ≪≫
        (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    (affineDerivedGlobalSections (𝟙 (Spec R))).map (δ.app F) ≫
        r.hom.app ((schemeDerivedDirectImage (pullback.snd f g)).obj F) ≫
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.map
          (d.hom.app F) =
      b.hom.app ((schemeDerivedDirectImage (pullback.fst f g)).obj F) ≫ c.hom.app F := by
  classical
  dsimp only
  let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
  let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let k := p (pullback.snd f g) g ≪≫
    eqToIso (congrArg (fun h ↦ derivedPullback h) (pullback.condition (f := f) (g := g)).symm) ≪≫
      (p (pullback.fst f g) f).symm
  let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
    ((a g).comp (a (pullback.snd f g))) k.hom
  let P := schemeDerivedDirectImage (pullback.fst f g)
  let Q := schemeDerivedDirectImage (pullback.snd f g)
  let Γ := affineDerivedGlobalSections (𝟙 (Spec R))
  let T := affineDerivedGlobalSections (pullback.snd f g)
  let ρ := (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory
  let α : P ⋙ schemeDerivedDirectImage f ⋙ Γ ⟶
      T ⋙ ρ :=
    Functor.whiskerRight δ Γ ≫ Functor.whiskerLeft Q r.hom ≫
      Functor.whiskerRight d.hom ρ
  let β : P ⋙ schemeDerivedDirectImage f ⋙ Γ ⟶
      T ⋙ ρ :=
    Functor.whiskerLeft P b.hom ≫ c.hom
  change α.app F = β.app F
  suffices h : α = β by exact NatTrans.congr_app h F
  have hI (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) ℤ)
      [I.IsKInjective] :
      α.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
      β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) := by
    let J := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let H := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let G := affineGlobalSections f
    have hG : IsIso (G.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj J.as))) :=
      exactComp_unit_isIso (RingedSpace.globalSectionsFunctor X.toRingedSpace)
        (affineGlobalSectionsRestriction f) _
        (isIso_directImage_globalSections_unit_on_kInjective (pullback.fst f g) I)
    have hH : IsIso (H.rightDerivedFunctorUnit.app J) := inferInstance
    have hU : IsIso ((Functor.rightDerivedFunctorCompUnit H G).app J) := by
      dsimp [Functor.rightDerivedFunctorCompUnit]
      infer_instance
    let U := (Functor.rightDerivedFunctorCompUnit H G).app J ≫
      (affineGlobalSectionsDerivedIso f).hom.app (P.obj (DerivedCategory.Qh.obj J)) ≫
      b.inv.app (P.obj (DerivedCategory.Qh.obj J))
    have : IsIso U := by dsimp [U]; infer_instance
    apply (cancel_epi U).mp
    have hleft := affineSections_square_mate_path_unit f g t b ht hb z d hz hd
      v r hv hr s hs J
    change U ≫ α.app (DerivedCategory.Qh.obj J) = U ≫ β.app (DerivedCategory.Qh.obj J)
    dsimp only [U, α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hleft.trans (hc J).symm
  apply NatTrans.ext
  funext E
  obtain ⟨J, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := HomotopyCategory.KInjectives.Qh) E
  obtain ⟨I, hKI, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
  rw [← cancel_epi ((P ⋙ schemeDerivedDirectImage f ⋙ Γ).map e.hom),
    α.naturality, β.naturality]
  exact congrArg (fun h ↦ h ≫ (T ⋙ ρ).map e.hom) (hI I)


end AlgebraicGeometry
