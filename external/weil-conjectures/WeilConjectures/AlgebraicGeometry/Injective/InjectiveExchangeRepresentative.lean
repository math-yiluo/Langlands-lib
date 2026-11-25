/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.Injective.InjectiveExchangeSourceTransport
import WeilConjectures.AlgebraicGeometry.Injective.InjectiveExchangeTargetTransport

/-! # Injective representative computation of the derived exchange

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-injective-exchange-representative).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.InjectiveExchangeRepresentative.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private lemma assemble_exchange {A B : Type*} [Category A] [Category B]
    (I : A ⥤ B) {X Y Z : A} {W : B}
    (a : W ⟶ I.obj X) (b : I.obj X ⟶ I.obj Y) (c : X ⟶ Y)
    (d : Y ⟶ Z) (e : X ⟶ Z) (t : W ⟶ I.obj Z)
    (hs : b = I.map c) (hm : c ≫ d = e) (ht : a ≫ I.map e = t) :
    a ≫ b ≫ I.map d = t := by
  rw [hs, ← Functor.map_comp, hm]
  exact ht

private lemma assemble_exchange_transport {A B : Type*} [Category A] [Category B]
    (I : A ⥤ B) {X Y Z : A} {V W : B}
    (a : V ⟶ W) (u : W ⟶ I.obj X) (b : W ⟶ I.obj Y) (c : X ⟶ Y)
    (d : Y ⟶ Z) (e : X ⟶ Z) (t : V ⟶ I.obj Z)
    (hs : b = u ≫ I.map c) (hm : c ≫ d = e) (ht : a ≫ u ≫ I.map e = t) :
    a ≫ b ≫ I.map d = t := by
  rw [hs, Category.assoc, ← Functor.map_comp, hm]
  exact ht

private lemma map_derivedCategory_ι_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (g : K ⟶ L) :
    F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map g) =
      DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map g) := rfl

private lemma map_comp_naturality {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (U : B ⥤ C) (P : A ⥤ D) (F : D ⥤ C)
    (θ : R ⋙ U ⟶ P ⋙ F) {X Y : A} {W : B}
    (u : W ⟶ R.obj X) (t : X ⟶ Y) :
    U.map (u ≫ R.map t) ≫ θ.app Y =
      (U.map u ≫ θ.app X) ≫ F.map (P.map t) := by
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_map] using
    congrArg (fun z ↦ U.map u ≫ z) (θ.naturality t)

-- Remote elaboration reached 200000 heartbeats in 21s after extracting generic proof steps.
/-- Compute the derived mate on the chosen injective representative, before sections.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, with the
factorization `Adjunction.derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-weil-pbc-injective-exchange-representative).

Proof: regard the injective complex as an object of the bounded-below homotopy
category. Lift q to its localization using the fully faithful inclusion of D⁺
into D. Apply the derived mate factorization and naturality in this lift of q.
The source direct-image unit is invertible on the injective complex; cancel it.
The definition of smallModel_sourceInjectiveDirectImageIso identifies its inverse with this
cancelled unit, followed by localization comparisons. The exact pullback
factorization identifies the underived exchange with Q of its termwise map.
Finally the defining unit compatibility of rightDerivedFunctorPlusCompatibility
changes the target bounded-below unit into the unbounded unit. Naturality moves
q.inv to the last factor. No target unit is inverted, so neither injectivity of
the pulled-back complex nor any acyclicity of it is required. -/
theorem smallModel_injectiveExchange_representative {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let T := P.mapDerivedCategoryPlus.obj K
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (.up ℤ)).app M
    U.mapDerivedCategoryFactors.inv.app L ≫
      U.mapDerivedCategory.map (smallModel_sourceInjectiveDirectImageIso f K J q).inv ≫
      DerivedCategory.Plus.ι.map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).app K) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T := by
  let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
    ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
  let H := (HomotopyCategory.Plus.quotient _).obj M
  let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
    DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Qh.obj H)
      (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
  let sq := (IsPullback.of_hasPullback f
    (Scheme.strictHenselizationStructuralMap s)).toCommSq
  let R := lowerStar AddCommGrpCat.{v + 1} f
  let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
  let P := upperStar AddCommGrpCat.{v + 1}
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
  let F := lowerStar AddCommGrpCat.{v + 1}
    (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
  let θ := (mateEquiv
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1} sq).hom))
  have fac := Adjunction.derivedPlus_mateEquiv_app_fac
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f)
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} (pullback.snd f
      (Scheme.strictHenselizationStructuralMap s)))
    (TwoSquare.mk _ _ _ _ (squareUpperStarIso AddCommGrpCat.{v + 1} sq).hom)
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1} sq).hom)
    (pullbackSquareComparison_hom_app_factorsh AddCommGrpCat.{v + 1} sq) H
  have hb :
      U.mapDerivedCategoryPlus.map
        (R.rightDerivedFunctorPlusUnith.app H ≫ R.rightDerivedFunctorPlus.map q'.inv) ≫
          θ.app K =
        U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap
              AddCommGrpCat.{v + 1} sq)).app H) ≫
          F.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj H) ≫
          F.rightDerivedFunctorPlus.map
            (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫
              P.mapDerivedCategoryPlus.map q'.inv) := by
    have hn := map_comp_naturality R.rightDerivedFunctorPlus U.mapDerivedCategoryPlus
      P.mapDerivedCategoryPlus F.rightDerivedFunctorPlus θ
      (R.rightDerivedFunctorPlusUnith.app H) q'.inv
    have hf := congrArg (fun z ↦ z ≫ F.rightDerivedFunctorPlus.map
      (P.mapDerivedCategoryPlus.map q'.inv)) fac
    refine hn.trans (hf.trans ?_)
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hs := smallModel_injectiveExchange_source_transport f K J q
  have hs' :
      U.mapDerivedCategory.map (smallModel_sourceInjectiveDirectImageIso f K J q).inv =
        U.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj M.obj)) ≫
        DerivedCategory.Plus.ι.map (U.mapDerivedCategoryPlus.map
          (R.rightDerivedFunctorPlusUnith.app H ≫ R.rightDerivedFunctorPlus.map q'.inv)) := by
    rw [hs, U.mapDerivedCategory.map_comp, ← DerivedCategory.Plus.ι.map_comp,
      map_derivedCategory_ι_map]
  have result := assemble_exchange_transport DerivedCategory.Plus.ι
    (U.mapDerivedCategoryFactors.inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj M.obj)) _ _ _ _ _ _ hs' hb
    (smallModel_injectiveExchange_target_transport f s K J q)
  exact result

end AlgebraicGeometry.Etale
