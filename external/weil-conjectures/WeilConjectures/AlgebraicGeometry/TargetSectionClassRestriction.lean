/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionCohomology

/-! # Restriction of target section classes

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
-- Keep the constructed maps named during type comparison; their bodies are unchanged.
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass

set_option backward.defeqAttrib.useBackward true in
private theorem sectionClass_restriction {Y : Scheme.{u}}
    (L : CochainComplex Y.Modules ℕ) (V : Y.Opens) (p : ℕ) :
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
    let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
    let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
    let r := (NatTrans.mapHomologicalComplex
      (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
        (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
      (ComplexShape.up ℕ)).app L
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op V) =
    ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op ⊤) ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  dsimp only
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
  let τ := Functor.whiskerLeft E (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op)
  have ht := NatTrans.app_homology τ (A.sc p)
  have hn := (E.map (sectionCohomologyTheta L p)).naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
      (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
    (ComplexShape.up ℕ)).app L
  have hc :
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
        ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom =
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
        (E.obj (A.homology p)).map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    rw [← cancel_epi ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).inv]
    simp only [Iso.inv_hom_id_assoc]
    have hr : (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r = (A.sc p).mapNatTrans τ := by
      ext <;> rfl
    change _ ≫ ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r) ≫ _ = _
    rw [hr]
    exact ht.symm
  rw [← Category.assoc, hc, Category.assoc]
  exact congrArg
    (fun t ↦ ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫ t) hn

-- Compose the cohomology comparison and section square before specializing their maps.
private theorem sectionClass_restriction_of_squares
    {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {q : A₀ ⟶ B₀} {a' : B₀ ⟶ B₁} {b' : B₁ ⟶ B₂} {k : B₂ ⟶ B₃}
    {r : A₂ ⟶ B₃} {c' : B₃ ⟶ B₄} {d' : B₄ ⟶ B₅} {s : A₄ ⟶ B₅}
    (hcoh : q ≫ a' ≫ b' ≫ k = a ≫ b ≫ r)
    (hsec : r ≫ c' ≫ d' = c ≫ d ≫ s) :
    (a ≫ b ≫ c ≫ d) ≫ s = q ≫ a' ≫ b' ≫ k ≫ c' ≫ d' := by
  calc
    (a ≫ b ≫ c ≫ d) ≫ s = (a ≫ b ≫ r) ≫ c' ≫ d' := by
      simp only [Category.assoc]
      rw [hsec]
    _ = (q ≫ a' ≫ b' ≫ k) ≫ c' ≫ d' := congrArg (· ≫ c' ≫ d') hcoh.symm
    _ = q ≫ a' ≫ b' ≫ k ≫ c' ≫ d' := by simp only [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
-- Comparing section complexes unfolds both the scheme and ringed-space interfaces.
private theorem restrictedResolution_sectionClass {Z Y : Scheme.{u}}
    (h : Z ⟶ Y) {G : Z.Modules} (I : InjectiveResolution G)
    (V : Y.Opens) (U : Z.Opens) (e : U = h ⁻¹ᵁ V)
    (R : RestrictedResolutionSections I U) (p : ℕ) :
    let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    resolutionSectionClass I L ⊤ (Iso.refl _) p ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
    moduleCohomologyRestriction U G p ≫
      resolutionSectionClass R.resolution L V
        (R.sections ≪≫ eqToIso (congrArg (fun T ↦
          ((RingedSpace.openModuleSections Z.toRingedSpace T).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) e)) p := by
  subst U
  let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hr := restrictedResolution_cohomology I (h ⁻¹ᵁ V) R p
  have hn := sectionClass_restriction L V p
  dsimp only at hn
  have hrmap :
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
          ((CategoryTheory.evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE (show h ⁻¹ᵁ V ≤ ⊤ from le_top)).op))
        (ComplexShape.up ℕ)).app I.cocomplex) =
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
          ((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE (show V ≤ ⊤ from le_top)).op))
        (ComplexShape.up ℕ)).app L) := by
    ext n
    rfl
  simp only [hrmap] at hr
  have hs := sectionClass_restriction_of_squares hr hn
  unfold resolutionSectionClass
  dsimp only
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  exact hs

set_option backward.defeqAttrib.useBackward true in
/-- The top-open germ of the class computed with a fixed global resolution equals
the germ of its target section class after restriction to the inverse-image open.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4) and Remark 20.14.2 (Tag 01FB).
(blueprint: lem-weil-pbc-target-section-class-restriction)

Proof: Put G = (tensorPullback (pullback.snd g f)).obj F and
W = (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V). Restrict the resolution K to W and
compose with D.target.comparison.inv. In degree zero, D.target.augmentation,
the inverse comparison equation, and naturality of the restriction-adjunction
unit show that this is an augmented lift of G to the pushforward of
D.target.resolution. Resolve this pushed complex into a termwise injective
complex by a quasi-isomorphism lambda. Use lambda times this lift as beta in
ModuleCohomologyFMapData, with source K and target D.target.resolution.
Its global-sections comparison induces an isomorphism by Tag 01EZ; the inverse
cancels the lambda factor on homology. Independence of ModuleCohomologyFMapData
identifies this calculation with moduleCohomologyRestriction W G p.
D.target.components now identifies the remaining complex map with restriction
from top to W. The equality flatBaseChangeOpenEquality transports W to
(pullback.fst g f) ⁻¹ᵁ (g ⁻¹ᵁ V). Naturality of the evaluation homology
comparison and of the presheaf map sectionCohomologyTheta identifies the resulting
section class with restriction of the top section class. Finally naturality of
the module morphism (K.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv
commutes this restriction with its section maps. This proves the displayed
morphism equality, with K fixed. Compose with the germ at y. Presheaf.germ_res cancels
the restriction from top to V. Top opens,
p = 0 and zero modules obey the same argument; no section-class isomorphism is
assumed. If V is empty the hypothesis y ∈ V is impossible. -/
theorem FlatBaseChangeOpenChoices.targetClass_restriction {X S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {K : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)}
    {V : S.Opens} (D : FlatBaseChangeOpenChoices f g F I K V) (p : ℕ)
    (y : S) (hy : y ∈ V)
    (eta : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace p).obj
      ((tensorPullback (pullback.snd g f)).obj F)) :
    TopCat.Presheaf.germ
      ((pushforward g).obj
        (((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F))).presheaf ⊤ y (by trivial)
      (Hom.app (K.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv ⊤
        (resolutionSectionClass K
          (((pushforward (pullback.fst g f)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K.cocomplex) ⊤ (Iso.refl _) p eta)) =
    TopCat.Presheaf.germ
      ((pushforward g).obj
        (((pushforward (pullback.fst g f)).rightDerived p).obj
          ((tensorPullback (pullback.snd g f)).obj F))).presheaf V y hy
      (D.targetClass p
        (moduleCohomologyFMap ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((restrictAdjunction ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
            ((tensorPullback (pullback.snd g f)).obj F)) p eta)) := by
  let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K.cocomplex
  let A := ((pushforward (pullback.fst g f)).rightDerived p).obj
    ((tensorPullback (pullback.snd g f)).obj F)
  let φ : L.homology p ⟶ A :=
    (K.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv
  have hs := restrictedResolution_sectionClass (pullback.fst g f) K (g ⁻¹ᵁ V)
    ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) (flatBaseChangeOpenEquality f g V) D.target p
  dsimp only at hs
  have hn := ((SheafOfModules.forget S'.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf S'.ringCatSheaf.obj).map φ).naturality
      (homOfLE (show g ⁻¹ᵁ V ≤ ⊤ from le_top)).op
  change (L.homology p).presheaf.map
      (homOfLE (show g ⁻¹ᵁ V ≤ ⊤ from le_top)).op ≫ Hom.app φ (g ⁻¹ᵁ V) =
    Hom.app φ ⊤ ≫ A.presheaf.map
      (homOfLE (show g ⁻¹ᵁ V ≤ ⊤ from le_top)).op at hn
  have hs' := congrArg (fun q ↦ q ≫ Hom.app φ (g ⁻¹ᵁ V)) hs
  simp only [Category.assoc] at hs'
  rw [hn] at hs'
  have hfinal : resolutionSectionClass K L ⊤ (Iso.refl _) p ≫ Hom.app φ ⊤ ≫
      A.presheaf.map (homOfLE (show g ⁻¹ᵁ V ≤ ⊤ from le_top)).op =
    moduleCohomologyRestriction ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))
      ((tensorPullback (pullback.snd g f)).obj F) p ≫ D.targetClass p := hs'
  have hv := ConcreteCategory.congr_hom hfinal eta
  simp only [AddCommGrpCat.comp_apply] at hv
  have hg := TopCat.Presheaf.germ_res_apply ((pushforward g).obj A).presheaf
    (homOfLE (show V ≤ ⊤ from le_top)) y hy
    (Hom.app φ ⊤ (resolutionSectionClass K L ⊤ (Iso.refl _) p eta))
  have ht := congrArg (fun x ↦
    TopCat.Presheaf.germ ((pushforward g).obj A).presheaf V y hy x) hv
  exact hg.symm.trans ht

end AlgebraicGeometry.Scheme.Modules
