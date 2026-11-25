/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLift
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleSetPullbackSheafEquivalence
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.DisjointComponentsLocallyConstantImage

/-!
# Locally constant direct image from finitely many universal-homeomorphism components

Source: smooth purity blueprint, final paragraph of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Direct image is locally constant when the source is a finite disjoint union of
open components each universally homeomorphic to the base.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, final paragraph;
steps 3 and 4 of `lem-weil-pbc-finite-map-generic-lisse-preservation`.
(blueprint: lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image).

Proof: Restrict E to each W i. These inverse images are lisse because pullback
preserves finite local constancy. The universal-homeomorphism equivalence of
small etale sites identifies each component direct image with inverse transport
through that equivalence. Transport a trivializing cover of the component sheaf.
Thus each component direct image has locally constant underlying set sheaf.
The sheaf condition for the disjoint component cover, pulled back to each
etale test object over Y, identifies f direct image E with the product of the
component direct images, naturally in the test object. Refine their finitely
many trivializing etale covers by a fibre product, and obtain a constant sheaf
on that cover. In the empty-family case X is empty by the cover hypothesis and
f direct image E is the zero abelian sheaf, whose underlying set sheaf is constant
singleton. Transport local constancy across the product identification. Finite
stalks are not asserted here: the caller proves them separately from the proved
finite-direct-image stalk formula. -/
theorem isLocallyConstant_finite_disjoint_universalHomeomorphism_directImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⨆ i, W i) = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (hW : ∀ i, IsUniversalHomeomorphism ((W i).ι ≫ f))
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsLisseEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E)) :=
    open CategoryTheory.Limits Opposite in by
  -- The available transport lemmas in RefinementPreservesFiniteLisse and
  -- PullbackFiniteLocallyConstant are private. Build the needed comparisons locally.
  have constant_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
      (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      [F.IsConstant X.smallEtaleTopology] :
      ((etaleSetPullback g).obj F).IsConstant Y.smallEtaleTopology := by
    have h := Sheaf.isConstant_sheafPullback g.Etale (K := Y.smallEtaleTopology) terminalIsTerminal
      (terminalIsTerminal.isTerminalObj g.Etale) F
    exact Sheaf.isConstant_congr _
      ((Functor.sheafPullbackConstruction.sheafPullbackIso g.Etale (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).app F)
  -- Compare localized restriction with set inverse image.
  have constant_over_iff {X : Scheme.{u}} (U : X.Etale)
      (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
      (F.over U).IsConstant (X.smallEtaleTopology.over U) ↔
        ((etaleSetPullback U.hom).obj F).IsConstant U.left.smallEtaleTopology := by
    let e : (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U) ≅
        (etaleSetPullback U.hom).obj F :=
      (fullyFaithfulSheafToPresheaf _ _).preimageIso
        (X := (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U))
        (Y := (Etale.localizationRestriction (Type (u + 1)) U.hom U.prop).obj F)
        (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) F.obj) ≪≫
          ((Classical.choose (etaleSetInverseImageRestriction U.hom)).app F).symm
    rw [← Sheaf.isConstant_sheafCongr_functor_iff
      (J := X.smallEtaleTopology.over U) (K := U.left.smallEtaleTopology)
      (Etale.overEquiv U) Over.mkIdTerminal (F.over U)]
    constructor
    · intro h
      have : ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
          (F.over U)).IsConstant U.left.smallEtaleTopology := h
      exact Sheaf.isConstant_congr _ e
    · intro h
      have := h
      exact Sheaf.isConstant_congr _ e.symm
  -- Reflect constancy through fully faithful inverse image.
  have constant_descend {X Y : Scheme.{u}} (p : Y ⟶ X)
      [IsUniversalHomeomorphism p] (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (hF : ((etaleSetPullback p).obj F).IsConstant Y.smallEtaleTopology) :
      F.IsConstant X.smallEtaleTopology := by
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      p.Etale (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology
    let e : etaleSetPullback p ≅ (Etale.sheafEquivalence (Type (u + 1)) p).inverse :=
      adj.leftAdjointUniq (Etale.sheafEquivalence (Type (u + 1)) p).symm.toAdjunction
    have : (etaleSetPullback p).IsEquivalence := Functor.isEquivalence_of_iso e.symm
    let ci : constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ etaleSetPullback p ≅
        constantSheaf Y.smallEtaleTopology (Type (u + 1)) :=
      (Functor.isoWhiskerLeft _
        (Functor.sheafPullbackConstruction.sheafPullbackIso p.Etale (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology)).symm ≪≫
        p.Etale.constantSheafsheafPullbackIso (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology terminalIsTerminal
          (terminalIsTerminal.isTerminalObj p.Etale)
    let := hF
    obtain ⟨a, ⟨i⟩⟩ := ((etaleSetPullback p).obj F).mem_essImage_of_isConstant
    exact Sheaf.isConstant_of_iso _
      ((etaleSetPullback p).preimageIso (i.symm ≪≫ (ci.app a).symm))
  -- Descend a cover and its constant restrictions through the site equivalence.
  have etaleSetLocallyConstant_descend {X Y : Scheme.{u}} (p : Y ⟶ X)
      [IsUniversalHomeomorphism p] (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (hF : IsLocallyConstantEtaleSheafOfSets ((etaleSetPullback p).obj F)) :
      IsLocallyConstantEtaleSheafOfSets F := by
    classical
    let : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
    have : p.Etale.IsEquivalence := Hom.isEquivalence_etale p
    obtain ⟨𝒰, h𝒰⟩ := hF
    obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
    let V (i : 𝒰.I₀) : X.Etale := p.Etale.objPreimage (𝒰.etalePrecoverageToEtale i)
    let e (i : 𝒰.I₀) : p.Etale.obj (V i) ≅ 𝒰.etalePrecoverageToEtale i :=
      p.Etale.objObjPreimageIso _
    have hinv (i : 𝒰.I₀) : (e i).inv.left ≫ pullback.snd (V i).hom p = 𝒰.f i :=
      MorphismProperty.Over.w (e i).inv
    let 𝒱 : Cover.{u} etalePrecoverage X :=
      { I₀ := 𝒰.I₀
        X i := (V i).left
        f i := (V i).hom
        mem₀ := by
          refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x => ?_, fun i => (V i).prop⟩
          obtain ⟨y, rfl⟩ := p.surjective x
          obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
          refine ⟨i, (pullback.fst (V i).hom p) ((e i).inv.left y'), ?_⟩
          change ((e i).inv.left ≫ pullback.fst (V i).hom p ≫ (V i).hom) y' =
            (𝒰.f i ≫ p) y'
          rw [pullback.condition, ← Category.assoc, hinv]
          rfl }
    refine ⟨𝒱, fun i => ?_⟩
    apply (constant_over_iff (𝒱.etalePrecoverageToEtale i) F).mpr
    change ((etaleSetPullback (V i).hom).obj F).IsConstant (V i).left.smallEtaleTopology
    have h₁ : ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)).IsConstant
        (𝒰.X i).smallEtaleTopology :=
      (constant_over_iff (𝒰.etalePrecoverageToEtale i) _).mp (h𝒰 i)
    change ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)).IsConstant
      (𝒰.etalePrecoverageToEtale i).left.smallEtaleTopology at h₁
    let := h₁
    have h₂ : ((etaleSetPullback (e i).hom.left).obj
        ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
        (pullback (V i).hom p).smallEtaleTopology := constant_pullback (e i).hom.left _
    change ((etaleSetPullback (e i).hom.left).obj
      ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
      (p.Etale.obj (V i)).left.smallEtaleTopology at h₂
    let := h₂
    have hsnd : pullback.snd (V i).hom p = (e i).hom.left ≫ 𝒰.f i :=
      (MorphismProperty.Over.w (e i).hom).symm
    let e' : (etaleSetPullback (pullback.fst (V i).hom p)).obj
        ((etaleSetPullback (V i).hom).obj F) ≅
        (etaleSetPullback (e i).hom.left).obj
          ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)) :=
      (c X (V i).left (pullback (V i).hom p) (V i).hom
        (pullback.fst (V i).hom p)).app F ≪≫
        eqToIso (congrArg (fun m => (etaleSetPullback m).obj F) pullback.condition) ≪≫
        ((c X Y (pullback (V i).hom p) p (pullback.snd (V i).hom p)).app F).symm ≪≫
        eqToIso (congrArg (fun m => (etaleSetPullback m).obj
          ((etaleSetPullback p).obj F)) hsnd) ≪≫
        ((c Y (𝒰.X i) (pullback (V i).hom p) (𝒰.f i) (e i).hom.left).app
          ((etaleSetPullback p).obj F)).symm
    have : ((etaleSetPullback (e i).hom.left).obj
        ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
        (pullback (V i).hom p).smallEtaleTopology := by
      change _ at h₂
      exact h₂
    exact constant_descend (pullback.fst (V i).hom p)
      ((etaleSetPullback (V i).hom).obj F) (Sheaf.isConstant_congr _ e'.symm)
  -- Transport the chosen trivializing cover through a sheaf isomorphism.
  have locallyConstant_of_iso {Z : Scheme.{u}}
      {F G : Sheaf Z.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
      (hF : IsLocallyConstantEtaleSheafOfSets F) :
      IsLocallyConstantEtaleSheafOfSets G := by
    obtain ⟨𝒰, h𝒰⟩ := hF
    refine ⟨𝒰, fun i => ?_⟩
    have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((Z.smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e)
  -- Compare abelian restriction after forgetting with localized set restriction.
  have underlying_isConstant_over_iff {X : Scheme.{u}} (U : X.Etale)
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Sheaf.IsConstant (X.smallEtaleTopology.over U)
        (((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U) ↔
      Sheaf.IsConstant U.left.smallEtaleTopology
        ((sheafCompose U.left.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj G)) := by
    let e := (sheafCompose U.left.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G)
    rw [← Sheaf.isConstant_sheafCongr_functor_iff (J := X.smallEtaleTopology.over U)
      (K := U.left.smallEtaleTopology) (Etale.overEquiv U) Over.mkIdTerminal]
    constructor
    · intro h
      have : Sheaf.IsConstant U.left.smallEtaleTopology ((sheafCompose U.left.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor.obj (G.over U))) := h
      exact Sheaf.isConstant_congr _ e
    · intro h
      have := h
      exact Sheaf.isConstant_congr _ e.symm
  -- Use the abelian/set comparison to pull back a constant underlying sheaf.
  have underlying_isConstant_upperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hG : Sheaf.IsConstant X.smallEtaleTopology
        ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :
      Sheaf.IsConstant Y.smallEtaleTopology
        ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G)) := by
    have hL : CategoryTheory.Limits.PreservesFiniteLimits (etaleSetPullback g) := by
      unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
      let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
        AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
      infer_instance
    obtain ⟨ea, hea⟩ := etaleInverseImageAbelianLift Y X g hL
    clear hea
    let S := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
    have : S.IsConstant X.smallEtaleTopology := hG
    let hT := MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) X
    have hc := Sheaf.isConstant_sheafPullback (K := Y.smallEtaleTopology)
      g.Etale hT (hT.isTerminalObj g.Etale) S
    let e := (Functor.sheafPullbackConstruction.sheafPullbackIso
      g.Etale
      (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology).app S
    have hconst : ((etaleSetPullback g).obj S).IsConstant Y.smallEtaleTopology :=
      Sheaf.isConstant_congr _ e
    exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _ (ea.app G).symm hconst
  -- Pull back the trivializing cover and compare the two composite inverse images.
  have underlying_locallyConstant_upperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hG : IsLocallyConstantEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :
      IsLocallyConstantEtaleSheafOfSets
        ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G)) := by
    obtain ⟨𝒰, h𝒰⟩ := hG
    refine ⟨𝒰.pullback₂ g, fun j ↦ ?_⟩
    rw [underlying_isConstant_over_iff _]
    have h₁ := (underlying_isConstant_over_iff (𝒰.etalePrecoverageToEtale j) G).mp (h𝒰 j)
    have h₂ := underlying_isConstant_upperStar (CategoryTheory.Limits.pullback.fst (𝒰.f j) g)
      ((Etale.upperStar AddCommGrpCat.{u + 1} (𝒰.f j)).obj G) h₁
    let e := ((Etale.upperStarComp AddCommGrpCat.{u + 1}
        (CategoryTheory.Limits.pullback.fst (𝒰.f j) g) (𝒰.f j)).app G).symm ≪≫
      eqToIso (congrArg (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj G)
        CategoryTheory.Limits.pullback.condition) ≪≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1}
        (CategoryTheory.Limits.pullback.snd (𝒰.f j) g) g).app G
    have hconst : Sheaf.IsConstant (CategoryTheory.Limits.pullback (𝒰.f j) g).smallEtaleTopology
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1}
            (CategoryTheory.Limits.pullback.fst (𝒰.f j) g)).obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (𝒰.f j)).obj G))) := h₂
    change Sheaf.IsConstant (CategoryTheory.Limits.pullback (𝒰.f j) g).smallEtaleTopology _
    exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e) hconst
  -- The equivalence unit identifies pullback of direct image with the component sheaf.
  have locallyConstant_universalHomeomorphism_image {X Y : Scheme.{u}}
      (f : X ⟶ Y) [IsUniversalHomeomorphism f]
      (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hE : IsLocallyConstantEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
      IsLocallyConstantEtaleSheafOfSets
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj E)) := by
    let S := (sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E
    let G := (Etale.lowerStar (Type (u + 1)) f).obj S
    change IsLocallyConstantEtaleSheafOfSets G
    apply etaleSetLocallyConstant_descend f G
    obtain ⟨e⟩ := Etale.etaleSetPullback_eq_sheafEquivalence f
    let c : (etaleSetPullback f).obj G ≅ S :=
      (e.app G).symm ≪≫ ((Etale.sheafEquivalence (Type (u + 1)) f).unitIso.app S).symm
    exact locallyConstant_of_iso c.symm hE
  apply isLocallyConstant_disjoint_components_directImage f n W hcover hdisjoint E
  intro i
  have : IsUniversalHomeomorphism ((W i).ι ≫ f) := hW i
  apply locallyConstant_universalHomeomorphism_image
  exact underlying_locallyConstant_upperStar (W i).ι E hE.1

end AlgebraicGeometry.Scheme
