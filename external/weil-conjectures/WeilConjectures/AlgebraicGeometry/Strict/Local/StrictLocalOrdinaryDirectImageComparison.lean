/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Base.BaseChangeGlobalHomology
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingleZero

/-! # Ordinary strict-local direct-image comparison

Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images in degree zero.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The bounded-below mate agrees with the exchange characterized on resolutions. -/
private theorem mate_eq_derivedExchange
    {X' X S' S : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : CommSq p f' f g) :
    (mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').derivedPlus
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom)) =
      derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq := by
  apply derivedBaseChangeMapPlus_ext
  intro K
  exact Adjunction.derivedPlus_mateEquiv_app_fac
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f')
    (TwoSquare.mk _ _ _ _ (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom)
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom)
    (pullbackSquareComparison_hom_app_factorsh AddCommGrpCat.{u + 1} sq) K

/-- The resolution factorization identifies degree-zero exchange with ordinary exchange. -/
private theorem ordinaryExchangeArrowIso
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [EnoughInjectives C] [EnoughInjectives C']
    (R : C ⥤ D) (R' : C' ⥤ D') (G : D ⥤ D') (P : C ⥤ C')
    [R.Additive] [R'.Additive] [G.Additive] [P.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteLimits R']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (τ : R ⋙ G ⟶ P ⋙ R')
    (δ : R.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus ⟶
      P.mapDerivedCategoryPlus ⋙ R'.rightDerivedFunctorPlus)
    (hδ : ∀ K : HomotopyCategory.Plus C,
      G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K) ≫
          δ.app (DerivedCategory.Plus.Qh.obj K) =
        G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app K) ≫
          R'.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K) ≫
          R'.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K))
    (F : C) :
    Nonempty (Arrow.mk ((DerivedCategory.Plus.homologyFunctor D' 0).map
      (δ.app ((DerivedCategory.Plus.singleFunctor C 0).obj F))) ≅ Arrow.mk (τ.app F)) := by
  let K₀ : CochainComplex.Plus C :=
    ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj F, 0, inferInstance⟩
  let K := (HomotopyCategory.Plus.quotient _).obj K₀
  have hu₁ := Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app
    R F
  have ha : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K))) := by
    have hN :=
      (G.mapDerivedCategoryPlusHomologyFunctorIso 0).hom.naturality
      (R.rightDerivedFunctorPlusUnith.app K)
    simp only [Functor.comp_map] at hN
    rw [← IsIso.inv_comp_eq] at hN
    rw [← hN]
    infer_instance
  -- Compare the single complex of `P.obj F` with the image of the single complex of F.
  let K₁ : CochainComplex.Plus C' :=
    ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj (P.obj F), 0,
      inferInstance⟩
  have hK : P.mapHomotopyCategoryPlus.obj K =
      (HomotopyCategory.Plus.quotient _).obj
        (P.mapCochainComplexPlus.obj K₀) := rfl
  let ψ : (HomotopyCategory.Plus.quotient _).obj K₁ ≅
      P.mapHomotopyCategoryPlus.obj K :=
    (HomotopyCategory.Plus.quotient _).mapIso (ObjectProperty.isoMk _
      (X := K₁) (Y := P.mapCochainComplexPlus.obj K₀)
      ((HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).app
        F).symm) ≪≫ eqToIso hK.symm
  have hu₂ := Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app
    R' (P.obj F)
  have hc : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      (R'.rightDerivedFunctorPlusUnith.app
        (P.mapHomotopyCategoryPlus.obj K))) := by
    have hN := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map
      (R'.rightDerivedFunctorPlusUnith.naturality ψ.hom)
    simp only [Functor.comp_map, Functor.map_comp] at hN
    exact IsIso.of_isIso_fac_left hN
  let H := DerivedCategory.Plus.homologyFunctor D' 0
  let a := G.mapDerivedCategoryPlus.map
    (R.rightDerivedFunctorPlusUnith.app K)
  let b := G.mapDerivedCategoryPlusFactorsh.hom.app
    (R.mapHomotopyCategoryPlus.obj K)
  let m := DerivedCategory.Plus.Qh.map
    ((NatTrans.mapHomotopyCategoryPlus τ).app K)
  let c := R'.rightDerivedFunctorPlusUnith.app
      (P.mapHomotopyCategoryPlus.obj K) ≫
    R'.rightDerivedFunctorPlus.map
      (P.mapDerivedCategoryPlusFactorsh.inv.app K)
  have ha' : IsIso (H.map a) := ha
  have hb' : IsIso (H.map b) := by dsimp only [b]; infer_instance
  have hc' : IsIso (H.map c) := by
    dsimp only [c]
    rw [Functor.map_comp]
    infer_instance
  have hfac : a ≫ δ.app (DerivedCategory.Plus.Qh.obj K) = b ≫ m ≫ c :=
    hδ K
  let e₂ := @Arrow.isoOfFac _ _ _ _ H _ _ _ _ _
    (δ.app (DerivedCategory.Plus.Qh.obj K)) m a b c hfac ha' hb' hc'
  -- step 3: in degree `0`, the map of complexes is the underived base-change map
  have e3eq : (DerivedCategory.Plus.homologyFunctor _ 0).map (DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus τ).app K)) =
      (DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
          τ (.up ℤ)).app K₀.obj))) := by
    change (DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Qh.map
      ((HomotopyCategory.Plus.ι _).map
        ((NatTrans.mapHomotopyCategoryPlus τ).app K))) = _
    rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    rfl
  have e₃ : Arrow.mk ((DerivedCategory.Plus.homologyFunctor _ 0).map (DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus τ).app K))) ≅
      Arrow.mk (τ.app F) := by
    rw [e3eq]
    exact Arrow.isoOfNatIso (Functor.isoWhiskerLeft (HomotopyCategory.quotient _ _)
        (DerivedCategory.homologyFunctorFactorsh _ 0) ≪≫
        HomotopyCategory.homologyFunctorFactors _ _ 0)
        (Arrow.mk ((NatTrans.mapHomologicalComplex τ
          (.up ℤ)).app K₀.obj)) ≪≫
      arrowIsoHomologyMapMapHomologicalComplexSingle _ _ _ F
  let ε : DerivedCategory.Plus.Qh.obj K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
    (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor _ 0).obj F)
      (Y := DerivedCategory.Plus.Qh.obj K)
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫
        (DerivedCategory.quotientCompQhIso _).symm.app _)).symm
  exact ⟨Arrow.isoMapApp δ (DerivedCategory.Plus.homologyFunctor _ 0) ε.symm ≪≫ e₂ ≪≫ e₃⟩

/-- The canonical ordinary exchange comparison on strict-local sections is invertible.
Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images, degree zero.
(blueprint: lem-weil-pbc-strict-local-ordinary-direct-image-comparison).

Proof: on the single complex F[0], factor the derived exchange through the levelwise
ordinary exchange and the two right-derived-functor units. Left exactness makes both
units invertible on H^0; exact inverse image commutes with H^0. The single-complex
homology isomorphisms identify the middle factor with the ordinary exchange. This gives
an isomorphism of arrows between H^0 of derived exchange and ordinary exchange.
The derived exchange is the mate used in strict-local base-change on global homology:
the latter satisfies the resolution factorization by the derived mate factorization
and the inverse-image square comparison equation, hence uniqueness identifies them.
Apply the small-model global-homology comparison to F[0] in degree zero and map the
arrow isomorphism through global sections. Invertibility transfers along this arrow
isomorphism. No stalk-map identification or closed-fibre transport is assumed. -/
theorem isIso_strictLocalOrdinaryDirectImageComparison
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{u + 1}).map
        ((baseChangeMap AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f
            (Scheme.strictHenselizationStructuralMap s)).toCommSq).app F)) := by
  let sq := (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq
  obtain ⟨e⟩ := ordinaryExchangeArrowIso
    ((f)_*[AddCommGrpCat.{u + 1}])
    ((pullback.snd f (Scheme.strictHenselizationStructuralMap s))_*[AddCommGrpCat.{u + 1}])
    ((Scheme.strictHenselizationStructuralMap s)^*[AddCommGrpCat.{u + 1}])
    ((pullback.fst f (Scheme.strictHenselizationStructuralMap s))^*[AddCommGrpCat.{u + 1}])
    (baseChangeMap AddCommGrpCat.{u + 1} sq)
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq)
    (derivedBaseChangeMapPlus_fac_app AddCommGrpCat.{u + 1} sq) F
  have hm := smallModel_isIso_strictHenselization_baseChange_globalHomology f s
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0
  rw [mate_eq_derivedExchange] at hm
  let Γ := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{u + 1}
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (Γ.mapArrow.mapIso e)).1 hm

end AlgebraicGeometry.Etale
