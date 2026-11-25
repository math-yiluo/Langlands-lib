/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The sheaf of derived local isomorphisms

Source: Stacks Project, Tag 09BV, isomorphism sheaves, with the bounded-derived adaptation
of lem-weil-pbc-compatible-finite-derived-trivializations
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf).

The presheaf uses actual isomorphisms in the derived categories of the localized etale
sites, identified with the sites of the source schemes. Its restriction maps are the
canonical exact pullbacks, transported by their composition comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

/-- Derived restriction of fixed-coefficient sheaves to an etale object, using the
existing exact inverse image. Source: Stacks Tag 03ED
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable abbrev localIsomorphismRestriction (V : X.Etale) :=
  (Etale.upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory

/-- Canonical comparison for successive etale restrictions.
Source: Stacks Tags 03ED and 05RU
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismRestrictionComp {V W : X.Etale} (f : V ⟶ W) :
    localIsomorphismRestriction X B V ≅ localIsomorphismRestriction X B W ⋙
      (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (Etale.upperStarComp (ModuleCat.{u + 1} B) f.left W.hom V.hom f.w.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

variable {X B}

/-- Restrict an actual local derived isomorphism along an arrow of the etale site.
Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismMap
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    {V W : X.Etale} (f : V ⟶ W)
    (e : (localIsomorphismRestriction X B W).obj A ≅
      (localIsomorphismRestriction X B W).obj K) :
    (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj K :=
  (localIsomorphismRestrictionComp X B f).app A ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.mapIso e ≪≫
    ((localIsomorphismRestrictionComp X B f).app K).symm

section RestrictionLaws

attribute [local irreducible] Etale.upperStar

private noncomputable abbrev restrictionTriangle {Y Z T : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ T) (h : Y ⟶ T := f ≫ g)
    (hh : h = f ≫ g := by cat_disch) :=
  Functor.mapDerivedCategoryTriangleIso
    (Etale.upperStarComp (ModuleCat.{u + 1} B) f g h hh)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem restrictionTriangle_assoc {Y Z T S : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ T) (h : T ⟶ S)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (restrictionTriangle (B := B) f (g ≫ h)).hom.app K ≫
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
        ((restrictionTriangle (B := B) g h).hom.app K) =
    (restrictionTriangle (B := B) (f ≫ g) h (f ≫ g ≫ h)
      (Category.assoc f g h).symm).hom.app K ≫
      (restrictionTriangle (B := B) f g).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj K) := by
  let F := Etale.upperStar (ModuleCat.{u + 1} B) h
  let G := Etale.upperStar (ModuleCat.{u + 1} B) g
  let H := Etale.upperStar (ModuleCat.{u + 1} B) f
  let a := Etale.upperStarComp (ModuleCat.{u + 1} B) f (g ≫ h)
  let b := Etale.upperStarComp (ModuleCat.{u + 1} B) g h
  let c := Etale.upperStarComp (ModuleCat.{u + 1} B) (f ≫ g) h
    (f ≫ g ≫ h) (Category.assoc f g h).symm
  let d := Etale.upperStarComp (ModuleCat.{u + 1} B) f g
  have hu := Etale.upperStarComp_assoc (ModuleCat.{u + 1} B) f g h
  have hassoc : F.associator G H = Iso.refl _ := by ext; rfl
  change a ≪≫ Functor.isoWhiskerRight b H ≪≫ F.associator G H =
    c ≪≫ Functor.isoWhiskerLeft F d at hu
  rw [hassoc, Iso.trans_refl] at hu
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hu
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hm
  have hwr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight b H) K
  have hwl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F d) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    at hwr hwl ha
  simp only [restrictionTriangle, Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hwr, ← reassoc_of% hwl]
  rw [← ha, reassoc_of% hm]

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionTriangle_assoc_named {Y Z T S : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ T) (h : T ⟶ S)
    (fg : Y ⟶ T) (hfg : fg = f ≫ g) (gh : Z ⟶ S) (hgh : gh = g ≫ h)
    (fgh : Y ⟶ S) (hfgh : fgh = f ≫ gh)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (restrictionTriangle (B := B) f gh fgh hfgh).hom.app K ≫
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.map
        ((restrictionTriangle (B := B) g h gh hgh).hom.app K) =
    (restrictionTriangle (B := B) fg h fgh
      (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
      (restrictionTriangle (B := B) f g fg hfg).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj K) := by
  subst fg
  subst gh
  subst fgh
  exact restrictionTriangle_assoc f g h K

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionTriangle_id (V : X.Etale)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (localIsomorphismRestrictionComp X B (𝟙 V)).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso
        (Etale.upperStarId (ModuleCat.{u + 1} B) V.left) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app
            ((localIsomorphismRestriction X B V).obj K) = 𝟙 _ := by
  let F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    Etale.upperStar (ModuleCat.{u + 1} B) V.hom
  let e := Etale.upperStarId (ModuleCat.{u + 1} B) V.left
  have hu := Etale.upperStarComp_id_left (ModuleCat.{u + 1} B) V.hom
  have hr : F.rightUnitor.symm = Iso.refl _ := by ext; rfl
  change Etale.upperStarComp (ModuleCat.{u + 1} B) (𝟙 V.left) V.hom V.hom _ =
    F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F e.symm at hu
  rw [hr, Iso.refl_trans] at hu
  have hwl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hunit := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hwl hunit
  simp only [localIsomorphismRestrictionComp, Iso.trans_hom, NatTrans.comp_app,
    localIsomorphismRestriction, Category.assoc]
  change (Functor.mapDerivedCategoryNatIso
    (Etale.upperStarComp (ModuleCat.{u + 1} B) (𝟙 V.left) V.hom V.hom _)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso F (Etale.upperStar
        (ModuleCat.{u + 1} B) (𝟙 V.left))).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (F.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app (F.mapDerivedCategory.obj K) = _
  rw [hu, ← reassoc_of% hwl]
  have hinv := congr_app (Iso.inv_hom_id
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e))) K
  have hsymm := congr_app
    (Functor.mapDerivedCategoryNatIso_symm (Functor.isoWhiskerLeft F e)) K
  change (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e.symm)).hom.app K =
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e)).inv.app K at hsymm
  simp only [NatTrans.comp_app, NatTrans.id_app] at hinv hunit
  rw [hsymm, ← Category.assoc, ← Category.assoc, hinv]
  erw [Category.id_comp]
  exact hunit

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
/-- The canonical local restriction maps obey the presheaf laws.
Source: Stacks Tags 03ED and 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf).
Proof: the underived inverse images have the identity and associativity comparisons
obtained from their adjunctions. Localization carries these comparisons and their
coherence identities to the derived category. In the conjugation defining the displayed
restriction map the intermediate comparison and its inverse cancel. The identity law
then follows from the identity comparison, and the composition law from associativity.
This applies to all derived objects and isomorphisms, without a boundedness assumption. -/
theorem localIsomorphismMap_laws
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (V : X.Etale) (e : (localIsomorphismRestriction X B V).obj A ≅
      (localIsomorphismRestriction X B V).obj K), localIsomorphismMap A K (𝟙 V) e = e) ∧
    (∀ {U V W : X.Etale} (f : U ⟶ V) (g : V ⟶ W)
      (e : (localIsomorphismRestriction X B W).obj A ≅
        (localIsomorphismRestriction X B W).obj K),
      localIsomorphismMap A K (f ≫ g) e =
        localIsomorphismMap A K f (localIsomorphismMap A K g e)) := by
  constructor
  · intro V e
    let δ := Functor.mapDerivedCategoryNatIso
      (Etale.upperStarId (ModuleCat.{u + 1} B) V.left) ≪≫
        Functor.mapDerivedCategoryIdIso _
    have hA := restrictionTriangle_id V A
    have hK := restrictionTriangle_id V K
    apply Iso.ext
    change (localIsomorphismRestrictionComp X B (𝟙 V)).hom.app A ≫
      (Etale.upperStar (ModuleCat.{u + 1} B) (𝟙 V.left)).mapDerivedCategory.map e.hom ≫
      (localIsomorphismRestrictionComp X B (𝟙 V)).inv.app K = e.hom
    have hdK : (localIsomorphismRestrictionComp X B (𝟙 V)).inv.app K =
        δ.hom.app ((localIsomorphismRestriction X B V).obj K) := by
      apply (cancel_epi ((localIsomorphismRestrictionComp X B (𝟙 V)).hom.app K)).mp
      simpa only [Iso.hom_inv_id_app] using hK.symm
    rw [hdK, δ.hom.naturality]
    change (localIsomorphismRestrictionComp X B (𝟙 V)).hom.app A ≫
      δ.hom.app ((localIsomorphismRestriction X B V).obj A) ≫ e.hom = e.hom
    rw [← Category.assoc, hA, Category.id_comp]
  · intro U V W f g e
    have hA := restrictionTriangle_assoc_named f.left g.left W.hom
      (f ≫ g).left rfl V.hom g.w.symm U.hom f.w.symm A
    have hK := restrictionTriangle_assoc_named f.left g.left W.hom
      (f ≫ g).left rfl V.hom g.w.symm U.hom f.w.symm K
    let F := (Etale.upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory
    let G := (Etale.upperStar (ModuleCat.{u + 1} B) g.left).mapDerivedCategory
    let H := (Etale.upperStar (ModuleCat.{u + 1} B) (f ≫ g).left).mapDerivedCategory
    let α := localIsomorphismRestrictionComp X B f
    let β := localIsomorphismRestrictionComp X B g
    let γ := localIsomorphismRestrictionComp X B (f ≫ g)
    let δ := restrictionTriangle (B := B) f.left g.left
    change α.hom.app A ≫ F.map (β.hom.app A) =
      γ.hom.app A ≫ δ.hom.app ((localIsomorphismRestriction X B W).obj A) at hA
    change α.hom.app K ≫ F.map (β.hom.app K) =
      γ.hom.app K ≫ δ.hom.app ((localIsomorphismRestriction X B W).obj K) at hK
    apply Iso.ext
    apply (cancel_mono
      (α.hom.app K ≫ F.map (β.hom.app K))).mp
    change (γ.hom.app A ≫ H.map e.hom ≫ γ.inv.app K) ≫
        (α.hom.app K ≫ F.map (β.hom.app K)) =
      (α.hom.app A ≫ F.map (β.hom.app A ≫ G.map e.hom ≫ β.inv.app K) ≫
        α.inv.app K) ≫ (α.hom.app K ≫ F.map (β.hom.app K))
    calc
      _ = γ.hom.app A ≫ H.map e.hom ≫
          δ.hom.app ((localIsomorphismRestriction X B W).obj K) := by
        rw [hK]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      _ = γ.hom.app A ≫ δ.hom.app ((localIsomorphismRestriction X B W).obj A) ≫
          F.map (G.map e.hom) := by
        erw [δ.hom.naturality]
        rfl
      _ = α.hom.app A ≫ F.map (β.hom.app A) ≫ F.map (G.map e.hom) := by
        rw [← Category.assoc, ← hA, Category.assoc]
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
        simp only [← F.map_comp, Iso.inv_hom_id_app]
        erw [Category.comp_id]

end RestrictionLaws

/-- The presheaf of isomorphisms in the derived categories of localized etale sites.
Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def derivedLocalIsomorphismPresheaf
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj V := (localIsomorphismRestriction X B V.unop).obj A ≅
    (localIsomorphismRestriction X B V.unop).obj K
  map f := TypeCat.ofHom (localIsomorphismMap A K f.unop)
  map_id V := ConcreteCategory.hom_ext _ _ ((localIsomorphismMap_laws A K).1 V.unop)
  map_comp f g := ConcreteCategory.hom_ext _ _ ((localIsomorphismMap_laws A K).2 g.unop f.unop)

/-- The sheafification of actual local derived isomorphisms; no arbitrary sheaf or
comparison map is chosen. Source: Stacks Tag 09BV, derived adaptation
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def derivedLocalIsomorphismSheaf
    (A K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
    (derivedLocalIsomorphismPresheaf A K)

section ProEtale

variable {Y : Scheme.{u}} (f : Y ⟶ X) {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Derived comparison followed by derived restriction to a pro-etale object. The same
formula is defined for any scheme map, with no change to the chosen derived categories.
Source: Stacks Tags 099R and 098K
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable abbrev localProEtaleComparison (R : Type (u + 1)) [CommRing R] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ⋙
    (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory

/-- The canonical comparison/coefficients interchange, obtained by localizing the mate
of sectionwise restriction. Source: Stacks Tags 099R and 03DA
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismComparisonCoefficients (q : R →+* S) :
    normalizationRestrict X.smallEtaleTopology q ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).mapDerivedCategory ⋙
        normalizationRestrict (ProEt.topology X) q :=
  Functor.mapDerivedCategoryCompIso
    (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X) ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X ⋙
      sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (normalizationPullbackIso X.smallEtaleTopology (toProEt X) (ProEt.topology X) q :
      sheafCompose X.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X ⋙
        sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ≪≫
  (Functor.mapDerivedCategoryCompIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X)
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))).symm

/-- The canonical pro-etale restriction/coefficients interchange, again the localization
of the specified mate. Source: Stacks Tags 098K and 03DA
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localIsomorphismProEtaleCoefficients (q : R →+* S) :
    normalizationRestrict (ProEt.topology X) q ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} S) f).mapDerivedCategory ⋙
        normalizationRestrict (ProEt.topology Y) q :=
  letI := ProEt.isContinuous_overPullback f
  Functor.mapDerivedCategoryCompIso
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (ProEtale.upperStar (ModuleCat.{u + 1} R) f) ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} R) f)
    (G := ProEtale.upperStar (ModuleCat.{u + 1} S) f ⋙
      sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))
    (normalizationPullbackIso (ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology Y) q :
      sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} R) f ≅
      ProEtale.upperStar (ModuleCat.{u + 1} S) f ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ≪≫
  (Functor.mapDerivedCategoryCompIso
    (ProEtale.upperStar (ModuleCat.{u + 1} S) f)
    (sheafCompose (ProEt.topology Y)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))).symm

/-- Combined canonical coefficient interchange for comparison and local restriction.
Source: Stacks Tags 099R and 098K
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localProEtaleComparisonCoefficients (q : R →+* S) :
    normalizationRestrict X.smallEtaleTopology q ⋙ localProEtaleComparison f R ≅
      localProEtaleComparison f S ⋙ normalizationRestrict (ProEt.topology Y) q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (localIsomorphismComparisonCoefficients q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (localIsomorphismProEtaleCoefficients f q) ≪≫
    (Functor.associator _ _ _).symm

/-- Pull a specified normalization arrow to the localized pro-etale site. This is its
actual inverse image followed by the canonical coefficient interchange, not an arbitrary
arrow with the same endpoints. Source: Stacks Tags 099R, 098K and 06YY
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf). -/
noncomputable def localProEtaleNormalization (q : R →+* S)
    {A : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (d : A ⟶ (normalizationRestrict X.smallEtaleTopology q).obj K) :
    (localProEtaleComparison f R).obj A ⟶
      (normalizationRestrict (ProEt.topology Y) q).obj
        ((localProEtaleComparison f S).obj K) :=
  (localProEtaleComparison f R).map d ≫
    (localProEtaleComparisonCoefficients f q).hom.app K

end ProEtale

end AlgebraicGeometry.Scheme
