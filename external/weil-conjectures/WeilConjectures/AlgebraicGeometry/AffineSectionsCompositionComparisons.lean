/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
-- Reuse its private exact-postcomposition and composite-derived-functor lemmas.
import all WeilConjectures.AlgebraicGeometry.AffineSectionsPushforwardNormalization

/-! # Normalized affine sections composition comparisons

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-sections-composition-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
private theorem deriveSectionsComparison
    {C D A : Type*} [Category C] [Category D] [Category A]
    [Abelian C] [Abelian D] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (DG : DerivedCategory D ⥤ DerivedCategory A)
    (DH : DerivedCategory C ⥤ DerivedCategory A)
    (uG : G.rightDerivedFunctor ≅ DG) (uH : H.rightDerivedFunctor ≅ DH)
    (s : F ⋙ G ≅ H)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    ∃ c : F.rightDerivedFunctor ⋙ DG ≅ DH,
      ∀ J : HomotopyCategory C (.up ℤ),
        (Functor.rightDerivedFunctorCompUnit F G).app J ≫
          uG.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
            c.hom.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
          H.rightDerivedFunctorUnit.app J ≫ uH.hom.app (DerivedCategory.Qh.obj J) := by
  have := composite_isRightDerived_of_acyclic F G h
  let eD := Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso _ (.up ℤ))
  let c := Functor.isoWhiskerLeft F.rightDerivedFunctor uG.symm ≪≫
    eD.symm ≪≫ Functor.rightDerivedFunctorNatIso s ≪≫ uH
  refine ⟨c, ?_⟩
  intro J
  have heD : (F ⋙ G).rightDerivedFunctorUnit.app J ≫
      eD.hom.app (DerivedCategory.Qh.obj J) =
      (Functor.rightDerivedFunctorCompUnit F G).app J := by
    simpa only [eD, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
        (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
        (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _) J
  have hfac : (Functor.rightDerivedFunctorCompUnit F G).app J ≫
      eD.inv.app (DerivedCategory.Qh.obj J) = (F ⋙ G).rightDerivedFunctorUnit.app J := by
    erw [← heD, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  simp only [c, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatTrans.comp_app, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hfac]
  dsimp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  rw [Functor.rightDerivedNatTrans_app_assoc]
  rfl

private theorem underivedSectionsComparison
    {A : CommRingCat.{u}} {X : Scheme.{u}} (h : X ⟶ Spec A) :
    ∃ t : RingedSpace.moduleDirectImage h.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec A)) ≅ affineGlobalSections h,
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (x : (affineGlobalSections h).obj M), (t.hom.app M) x = x := by
  let α := ((Scheme.ΓSpecIso A).inv ≫ ((𝟙 (Spec A)) : Spec A ⟶ Spec A).appTop).hom
  let δ := h.appTop.hom
  let β := ((Scheme.ΓSpecIso A).inv ≫ h.appTop).hom
  have he : β = δ.comp α := by
    simp only [β, δ, α, Scheme.Hom.id_appTop, Category.comp_id]
    rfl
  let t := Functor.isoWhiskerLeft (RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (ModuleCat.restrictScalarsComp' α δ β he).symm
  refine ⟨t, ?_⟩
  intro M x
  rfl

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

private theorem affineSectionsAcyclic
    {A : CommRingCat.{u}} {X : Scheme.{u}} (h : X ⟶ Spec A) :
    ∀ (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      [I.IsKInjective],
      IsIso ((affineGlobalSections (𝟙 (Spec A))).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  intro I hI
  exact exactComp_unit_isIso (RingedSpace.globalSectionsFunctor (Spec A).toRingedSpace)
    (affineGlobalSectionsRestriction (𝟙 (Spec A))) _
    (isIso_directImage_globalSections_unit_on_kInjective h I)

/-- Normalized sections comparisons for f, its base change, and g itself.
This statement concerns only right-derived composition; it has no input E,
quasi-coherence hypothesis, extension functor, or base-change map.
Source: Stacks, cohomology.tex, Tag 0D5T (lemma-derived-pushforward-composition), and
perfect.tex, Tag 0AA7, restriction of the canonical comparison to the base.
(blueprint: lem-pc-affine-sections-composition-comparisons).
Proof:
1. For f and f', evaluate direct image at the whole open. The inverse image
of that open is the whole open. Sections are unchanged. Compose the scalar
restriction maps and cancel GammaSpecIso to obtain the identity t and z.
For g the same calculation gives v: the B-action restricted along the
canonical R-to-B map is precisely the action on sections of g_*.
2. A direct image of a K-injective complex is acyclic for global sections.
Exact scalar restriction preserves the invertibility of that derived unit.
Consequently the composite right-derived unit computes the right-derived
functor of each underived composite, even for unbounded complexes.
3. Right-derived uniqueness, followed by deriving t, z, and v and the exact
restriction comparisons, gives b, d, and r. The factorization equations for
these comparisons are exactly the three displayed derived-unit equations.
These constructions are simultaneous and require no Tor independence. -/
theorem exists_affineSectionsCompositionComparisons
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    ∃ t : RingedSpace.moduleDirectImage (f).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅ affineGlobalSections (f),
      ∃ b : schemeDerivedDirectImage (f) ⋙
        affineDerivedGlobalSections (𝟙 (Spec R)) ≅ affineDerivedGlobalSections (f),
      ∃ z : RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec B)) ≅ affineGlobalSections (pullback.snd f g),
      ∃ d : schemeDerivedDirectImage (pullback.snd f g) ⋙
        affineDerivedGlobalSections (𝟙 (Spec B)) ≅ affineDerivedGlobalSections (pullback.snd f g),
      ∃ v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g),
      ∃ r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory,
      (∀ (M : SheafOfModules.{u} (moduleRings (X).toRingedSpace))
        (x : (affineGlobalSections (f)).obj M), (t.hom.app M) x = x) ∧
      (∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (X).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (f).toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage (f)).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (f)).rightDerivedFunctorUnit.app J ≫
        (affineGlobalSectionsDerivedIso (f)).hom.app (DerivedCategory.Qh.obj J)) ∧
      (∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (affineGlobalSections (pullback.snd f g)).obj M), (z.hom.app M) x = x) ∧
      (∀ J : HomotopyCategory
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
        (affineGlobalSectionsDerivedIso (pullback.snd f g)).hom.app (DerivedCategory.Qh.obj J)) ∧
      (∀ (M : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (x : (affineGlobalSections (𝟙 (Spec B))).obj M), (v.hom.app M) x = x) ∧
      (∀ J : HomotopyCategory
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
          (DerivedCategory.Qh.obj J))  := by
  let t := (underivedSectionsComparison f).choose
  have ht := (underivedSectionsComparison f).choose_spec
  let z := (underivedSectionsComparison (pullback.snd f g)).choose
  have hz := (underivedSectionsComparison (pullback.snd f g)).choose_spec
  have hb₀ := deriveSectionsComparison
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
    (affineGlobalSections (𝟙 (Spec R))) (affineGlobalSections f)
    (affineDerivedGlobalSections (𝟙 (Spec R))) (affineDerivedGlobalSections f)
    (affineGlobalSectionsDerivedIso (𝟙 (Spec R))) (affineGlobalSectionsDerivedIso f)
    t (affineSectionsAcyclic f)
  let b := hb₀.choose
  have hb := hb₀.choose_spec
  have hd₀ := deriveSectionsComparison
    (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom)
    (affineGlobalSections (𝟙 (Spec B))) (affineGlobalSections (pullback.snd f g))
    (affineDerivedGlobalSections (𝟙 (Spec B)))
    (affineDerivedGlobalSections (pullback.snd f g))
    (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
    (affineGlobalSectionsDerivedIso (pullback.snd f g)) z (affineSectionsAcyclic _)
  let d := hd₀.choose
  have hd := hd₀.choose_spec
  let α := ((Scheme.ΓSpecIso R).inv ≫ ((𝟙 (Spec R)) : Spec R ⟶ Spec R).appTop).hom
  let δ := g.appTop.hom
  let β := ((Scheme.ΓSpecIso B).inv ≫ ((𝟙 (Spec B)) : Spec B ⟶ Spec B).appTop).hom
  let ρ := affineBaseRingMap g
  have he : δ.comp α = β.comp ρ := by
    dsimp [δ, α, β, ρ, affineBaseRingMap]
    change ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom =
      ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫
        (Scheme.ΓSpecIso B).hom ≫ (Scheme.ΓSpecIso B).inv).hom
    simp only [Iso.hom_inv_id, Category.comp_id]
  let v := Functor.isoWhiskerLeft (RingedSpace.globalSectionsFunctor (Spec B).toRingedSpace)
    ((ModuleCat.restrictScalarsComp α δ).symm ≪≫
      ModuleCat.restrictScalarsComp' ρ β (δ.comp α) he)
  let ur := Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (affineGlobalSections (𝟙 (Spec B))) (ModuleCat.restrictScalars.{u} ρ) ≪≫
    Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
      (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory
  have hr₀ := deriveSectionsComparison
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (affineGlobalSections (𝟙 (Spec R)))
    (affineGlobalSections (𝟙 (Spec B)) ⋙ ModuleCat.restrictScalars.{u} ρ)
    (affineDerivedGlobalSections (𝟙 (Spec R)))
    (affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
      (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory)
    (affineGlobalSectionsDerivedIso (𝟙 (Spec R))) ur v (affineSectionsAcyclic g)
  let r := hr₀.choose
  have hr := hr₀.choose_spec
  exact ⟨t, b, z, d, v, r, ht, hb, hz, hd, fun M x ↦ rfl, hr⟩

end AlgebraicGeometry
