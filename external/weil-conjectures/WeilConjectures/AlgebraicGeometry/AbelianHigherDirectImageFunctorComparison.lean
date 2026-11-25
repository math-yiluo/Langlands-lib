/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Natural abelian higher-image comparison

Source: Stacks Project, Tag 03Q8.
(blueprint: lem-sbc-abelian-higher-image-sheafification-functor-iso)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

-- The adjunction checks a nested derived-Hom and sheafification comparison.
private theorem homologySheafificationIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})] :
    Nonempty (preadditiveYoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (AbelianComparison.freeSheaf J ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      presheafToSheaf J AddCommGrpCat.{u + 1} ≅
    DerivedCategory.Plus.homologyFunctor
      (Sheaf J AddCommGrpCat.{u + 1}) 0) := by
  let B := AbelianComparison.freeSheaf J
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf J AddCommGrpCat.{u + 1}) 0
  let V := preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (B ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
  let ψ : V ⟶ H ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1} :=
    { app := fun K ↦ AbelianComparison.derivedHomToHomology K ≫
        AbelianComparison.freeSheafSections (H.obj K)
      naturality := by
        intro K K' f
        ext ⟨U⟩ z
        change (AbelianComparison.freeSheafSections (H.obj K')).app (Opposite.op U)
            ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
              (B.obj U) ≫ H.map (z ≫ f)) =
          (H.map f).hom.app (Opposite.op U)
            ((AbelianComparison.freeSheafSections (H.obj K)).app (Opposite.op U)
              ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
                (B.obj U) ≫ H.map z))
        rw [H.map_comp, ← Category.assoc]
        simpa only [AbelianComparison.freeSheafHomEquiv_apply] using
          AbelianComparison.freeSheafHomEquiv_comp U
            ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
              (B.obj U) ≫ H.map z) (H.map f) }
  let adj := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let α : V ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} ⟶ H :=
    ((adj.whiskerRight (DerivedCategory.Plus
      (Sheaf J AddCommGrpCat.{u + 1}))).homEquiv V H).symm ψ
  have hi (K : DerivedCategory.Plus
      (Sheaf J AddCommGrpCat.{u + 1})) : IsIso (α.app K) := by
    have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    obtain ⟨_, _⟩ := AbelianComparison.isLocallyBijective_derivedHomToHomology K
    have hfac : toSheafify J (V.obj K) ≫ (α.app K).hom = ψ.app K := by
      have he := (adj.homEquiv (V.obj K) (H.obj K)).apply_symm_apply (ψ.app K)
      rw [Adjunction.homEquiv_unit] at he
      exact he
    refine (Sheaf.isLocallyBijective_iff_isIso (α.app K)).1 ⟨?_, ?_⟩
    · have : Presheaf.IsLocallyInjective J
          (toSheafify J (V.obj K) ≫ (α.app K).hom) := by
        rw [hfac]
        dsimp only [ψ]
        infer_instance
      exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
        J (toSheafify J _) (α.app K).hom
    · have : Presheaf.IsLocallySurjective J
          (toSheafify J (V.obj K) ≫ (α.app K).hom) := by
        rw [hfac]
        dsimp only [ψ]
        infer_instance
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J
        (toSheafify J _) (α.app K).hom
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α⟩


private noncomputable def adjunctionYonedaIso
    {C D E : Type*} [Category C] [Category.{u + 1} D] [Category.{u + 1} E]
    [Preadditive D] [Preadditive E] (B : C ⥤ D)
    {L : D ⥤ E} {R : E ⥤ D} [L.Additive] (adj : L ⊣ R) :
    preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (B ⋙ L).op ≅
      R ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj B.op :=
  NatIso.ofComponents
    (fun K ↦ AbelianComparison.adjunctionPresheafIso B adj K) (by
      intro K K' f
      ext U z
      exact adj.homEquiv_naturality_right z f)

private noncomputable def yonedaRestrictionIso
    {C D : Type*} [Category C] [Category.{u + 1} D] [Preadditive D]
    {B B' : C ⥤ D} (e : B ≅ B') :
    preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj B.op ≅
      preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj B'.op :=
  NatIso.ofComponents
    (fun K ↦ Functor.isoWhiskerRight (NatIso.op e.symm) (preadditiveYoneda.obj K)) (by
      intro K K' f
      ext U z
      change e.inv.app U.unop ≫ (z ≫ f) = (e.inv.app U.unop ≫ z) ≫ f
      exact (Category.assoc _ _ _).symm)

/-- The sheafified raw derived-Hom functor is naturally isomorphic to higher
 direct image, in the coefficient sheaf. No qcqs or continuity hypothesis is used.

Source: Stacks Project, Tag 03Q8 (lemma-higher-direct-images), with Tags 072W
and 0BKV for the sheafification calculation.

Proof: Let B send an etale X-scheme U to the free abelian sheaf of U. Derived
adjunction and the inverse-image single-functor comparison identify
Hom((h^*B(U))[0], F[0][q]) with Hom(B(U)[0], Rh_*(F[0][q])). The identification
commutes with maps of F by right naturality of the adjunction. Send a derived
map to its zeroth homology and evaluate at the represented identity generator.
This gives a presheaf map to H^0(Rh_*(F[0][q])). On an injective complex every
homology section locally lifts to a cycle, giving a chain map from B(U)[0].
A class whose section is zero locally lifts to a boundary, so that chain map
is locally null-homotopic. The map is therefore locally bijective, and its
sheafification is invertible. Adjunction naturality, functoriality of homology
and evaluation at the same generator make this comparison natural in F.
Finally use the natural shift comparison for Rh_* and the homology shift
isomorphism to replace H^0(Rh_*(F[0][q])) by H^q(Rh_*F[0]). Compose the resulting
natural isomorphisms. For q=0 this is the usual sections comparison; for empty
schemes the same local-bijection proof applies. No arbitrary object is chosen.
(blueprint: lem-sbc-abelian-higher-image-sheafification-functor-iso) -/
theorem nonempty_abelianHigherDirectImage_sheafificationFunctorIso
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℕ) :
    Nonempty
      ((DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        shiftFunctor _ (q : ℤ) ⋙ preadditiveYoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (uliftYoneda.{u + 1} ⋙
            (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
            presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            upperStar AddCommGrpCat.{u + 1} h ⋙
            DerivedCategory.Plus.singleFunctor _ 0).op) ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      DerivedCategory.Plus.singleFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)) := by
  let B := AbelianComparison.freeSheaf X.smallEtaleTopology
  let S := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let R := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h
  let : R.CommShift ℤ :=
    (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlusCommShift
  let E := S ⋙ shiftFunctor _ (q : ℤ)
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let V := preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (B ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
  let P := E ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (B ⋙ upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
  let F := (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus
  let A := B ⋙ DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let c : A ⋙ F ≅
      B ⋙ upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0 :=
    Functor.isoWhiskerLeft B
      ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0)
  let e : P ≅ E ⋙ R ⋙ V :=
    Functor.isoWhiskerLeft E (yonedaRestrictionIso c.symm) ≪≫
      Functor.isoWhiskerLeft E
        (adjunctionYonedaIso A
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus)
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  obtain ⟨eH⟩ := homologySheafificationIso X.smallEtaleTopology
  let e' : P ⋙ L ≅ E ⋙ R ⋙ H₀ :=
    Functor.isoWhiskerRight e L ≪≫
      Functor.associator E (R ⋙ V) L ≪≫
      Functor.isoWhiskerLeft E (Functor.associator R V L) ≪≫
      Functor.isoWhiskerLeft E
        (Functor.isoWhiskerLeft R eH)
  let τ : shiftFunctor _ (q : ℤ) ⋙ R ⋙ H₀ ≅ R ⋙ Hq :=
    (Functor.associator (shiftFunctor _ (q : ℤ)) R H₀).symm ≪≫
      Functor.isoWhiskerRight (R.commShiftIso (q : ℤ)) H₀ ≪≫
      Functor.associator R (shiftFunctor _ (q : ℤ)) H₀ ≪≫
      Functor.isoWhiskerLeft R (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
  exact ⟨e' ≪≫ Functor.associator S (shiftFunctor _ (q : ℤ)) (R ⋙ H₀) ≪≫
    Functor.isoWhiskerLeft S τ⟩

end AlgebraicGeometry.Etale
