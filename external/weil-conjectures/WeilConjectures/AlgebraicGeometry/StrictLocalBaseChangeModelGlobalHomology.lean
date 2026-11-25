/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Global homology of base change to a chosen strict-local model

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency true in
private theorem isIso_isoSquare (B : Type (u + 2)) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    [IsIso g] [IsIso g'] :
    IsIso (derivedBaseChangeMapPlus B sq) := by
  have hInst1 := isEquivalence_upperStar B g'
  have hK : ∀ K, IsIso ((derivedBaseChangeMapPlus B sq).app K) := by
    intro K
    obtain ⟨n, hn⟩ := K.2
    have hInst2 : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
    let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
    let P := (HomotopyCategory.Plus.quotient _).obj M
    suffices IsIso ((derivedBaseChangeMapPlus B sq).app
        (DerivedCategory.Plus.Qh.obj P)) by
      rw [← NatTrans.isIso_app_iff_of_iso _
        ((DerivedCategory.Plus.quotientCompQhIso _).app M ≪≫ e)]
      exact this
    have hM : ∀ m, (f')_*[B].rightAcyclic
        ((((g')^*[B]).mapCochainComplexPlus.obj M).obj.X m) := fun m ↦ by
      have hInst3 : Injective (M.obj.X m) := (L.obj.X m).2
      have hInst4 : Injective ((((g')^*[B]).mapCochainComplexPlus.obj M).obj.X m) :=
        Functor.injective_obj (g')^*[B] (M.obj.X m)
      exact (f')_*[B].rightAcyclic_of_injective _
    have hInst5 : IsIso ((f')_*[B].rightDerivedFunctorPlusUnith.app
        (((g')^*[B]).mapHomotopyCategoryPlus.obj P)) :=
      (f')_*[B].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
        (((g')^*[B]).mapCochainComplexPlus.obj M) hM
    have hInst6 : IsIso ((f)_*[B].rightDerivedFunctorPlusUnith.app P) := by
      dsimp only [P, M]
      infer_instance
    have hfac := derivedBaseChangeMapPlus_fac_app B sq P
    have hInst7 : IsIso (((g)^*[B]).mapDerivedCategoryPlus.map
        ((f)_*[B].rightDerivedFunctorPlusUnith.app P) ≫
        (derivedBaseChangeMapPlus B sq).app (DerivedCategory.Plus.Qh.obj P)) := by
      rw [hfac]
      have hInst8 : IsIso (baseChangeMap B sq) := inferInstance
      have hInst9 : IsIso ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap B sq)).app P) :=
        inferInstance
      have hInst10 : IsIso (((g)^*[B]).mapDerivedCategoryPlusFactorsh.hom.app
          ((f)_*[B].mapHomotopyCategoryPlus.obj P)) := inferInstance
      have hInst11 : IsIso (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap B sq)).app P)) := inferInstance
      have hInst12 : IsIso ((f')_*[B].rightDerivedFunctorPlusUnith.app
          (((g')^*[B]).mapHomotopyCategoryPlus.obj P)) := inferInstance
      have hInst13 : IsIso ((f')_*[B].rightDerivedFunctorPlus.map
          (((g')^*[B]).mapDerivedCategoryPlusFactorsh.inv.app P)) := inferInstance
      exact IsIso.comp_isIso' hInst10
        (IsIso.comp_isIso' hInst11 (IsIso.comp_isIso' hInst12 hInst13))
    exact IsIso.of_isIso_comp_left
      (((g)^*[B]).mapDerivedCategoryPlus.map ((f)_*[B].rightDerivedFunctorPlusUnith.app P)) _
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency true in
private theorem isIso_globalHomology_upperStar (B : Type (u + 2)) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {Y Z : Scheme.{u}} (e : Z ≅ Y)
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology B)}
    (m : K ⟶ L) (n : ℤ)
    [IsIso ((Sheaf.Γ Y.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map m))] :
    IsIso ((Sheaf.Γ Z.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        (((e.hom)^*[B]).mapDerivedCategoryPlus.map m))) := by
  let U := (e.hom)^*[B]
  let R := (e.hom)_*[B]
  let GY := Sheaf.Γ Y.smallEtaleTopology B
  let GZ := Sheaf.Γ Z.smallEtaleTopology B
  have hInst14 := isEquivalence_upperStar B e.hom
  let t : GY ≅ U ⋙ GZ :=
    (Functor.leftUnitor GY).symm ≪≫
      Functor.isoWhiskerRight (asIso (upperStarLowerStarAdjunction B e.hom).unit) GY ≪≫
      Functor.associator U R GY ≪≫
      Functor.isoWhiskerLeft U (lowerStarCompGlobalSectionsIso B e.hom)
  let h := U.mapDerivedCategoryPlusHomologyFunctorIso n
  let a := Functor.isoWhiskerRight h.symm GZ ≪≫
    Functor.associator (DerivedCategory.Plus.homologyFunctor _ n) U GZ ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor _ n) t.symm
  apply (NatIso.isIso_map_iff a m).mpr
  change IsIso (GY.map ((DerivedCategory.Plus.homologyFunctor _ n).map m))
  infer_instance

set_option backward.isDefEq.respectTransparency true in
private theorem derivedBaseChangeMapPlus_app_eq_mate
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    (derivedBaseChangeMapPlus B sq).app K =
      (mateEquiv (upperStarLowerStarAdjunction B f).derivedPlus
        (upperStarLowerStarAdjunction B f').derivedPlus
        (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom)).app K := by
  have h := derivedBaseChangeMapPlus_ext B sq
    (mateEquiv (upperStarLowerStarAdjunction B f).derivedPlus
      (upperStarLowerStarAdjunction B f').derivedPlus
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom))
    (fun N ↦ Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction B f)
      (upperStarLowerStarAdjunction B f')
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso B sq).hom)
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom)
      (pullbackSquareComparison_hom_app_factorsh B sq) N)
  exact congrArg (fun t ↦ t.app K) h.symm

set_option backward.isDefEq.respectTransparency true in
private theorem isIso_globalHomology_of_mate
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    (h : IsIso ((Sheaf.Γ Y'.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((mateEquiv (upperStarLowerStarAdjunction B f).derivedPlus
          (upperStarLowerStarAdjunction B f').derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom)).app K)))) :
    IsIso ((Sheaf.Γ Y'.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus B sq).app K))) := by
  rw [derivedBaseChangeMapPlus_app_eq_mate B sq K]
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem isIso_globalHomology_isoModel
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {X S Y Z P X₀ : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ S)
    (p : P ⟶ X) (f' : P ⟶ Y) (sq₁ : IsPullback p f' f j)
    (e : Z ≅ Y) (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Z)
    (sq₀ : IsPullback p₀ f₀ f (e.hom ≫ j))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) (n : ℤ)
    [hcanonical : IsIso ((Sheaf.Γ Y.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus B sq₁.toCommSq).app K)))] :
    IsIso ((Sheaf.Γ Z.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus B sq₀.toCommSq).app K))) := by
  let b := sq₁.lift p₀ (f₀ ≫ e.hom) (by simpa only [Category.assoc] using sq₀.w)
  have hb : b ≫ p = p₀ := sq₁.lift_fst _ _ _
  have sq₂ : IsPullback b f₀ f' e.hom := sq₀.of_right' sq₁
  have hbIso : IsIso b := sq₂.isIso_fst_of_isIso
  have hcomparison : IsIso (derivedBaseChangeMapPlus B sq₂.toCommSq) :=
    isIso_isoSquare B sq₂.toCommSq
  have hp := derivedBaseChangeMapPlus_paste_horiz B sq₁.toCommSq sq₂.toCommSq
    (sq₂.paste_horiz sq₁).toCommSq
  have hcanonicalPullback : IsIso ((Sheaf.Γ Z.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        (((e.hom)^*[B]).mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus B sq₁.toCommSq).app K)))) :=
    isIso_globalHomology_upperStar B e _ n
  have ht : IsIso ((Sheaf.Γ Z.smallEtaleTopology B).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus B (sq₂.paste_horiz sq₁).toCommSq).app K))) := by
    rw [hp]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Functor.map_comp]
    exact IsIso.comp_isIso' (by infer_instance)
      (IsIso.comp_isIso' hcanonicalPullback
        (IsIso.comp_isIso' (by infer_instance) (by infer_instance)))
  have transfer (q : X₀ ⟶ X) (h : q = b ≫ p)
      (sq : IsPullback q f₀ f (e.hom ≫ j)) :
      IsIso ((Sheaf.Γ Z.smallEtaleTopology B).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((derivedBaseChangeMapPlus B sq.toCommSq).app K))) := by
    subst q
    exact ht
  exact transfer p₀ hb.symm sq₀

set_option backward.isDefEq.respectTransparency true in
/-- Global sections of homology of base change to any strict-henselization model
are invertible. No geometric stalk or choice of its field occurs in this assertion.
Source: Stacks Project, Tag 03Q9 (theorem-higher-direct-images), and Tag 03QO.
(blueprint: lem-weil-pbc-strict-local-base-change-model-global-homology).

Proof:
1. Apply `isIso_strictHenselization_baseChange_globalHomology` to f, s, K and n.
Compare the mate in that theorem with `derivedBaseChangeMapPlus` on injective
representatives using `Adjunction.derivedPlus_mateEquiv_app_fac` and
`pullbackSquareComparison_hom_app_factorsh`. Their equality follows from
`derivedBaseChangeMapPlus_ext`.
2. Set j = strictLocalizationToBase s and P = pullback f j. The map
b = pullback.lift p₀ (f₀ ≫ eA.hom) sq₀.w is an isomorphism: the square with b,
f₀, pullback.snd f j and eA.hom is cartesian by pullback cancellation, and its
bottom edge is an isomorphism. Its derived mate is invertible, by the formula
`derivedBaseChangeMapPlus_fac_app` on injectives and exact inverse-image equivalences.
3. Use `derivedBaseChangeMapPlus_paste_horiz` for the canonical square and this
isomorphism square. It expresses the chosen mate as the canonical mate pulled back
along eA.hom, composed with the isomorphism mate and composition isomorphisms.
Homology commutes with exact inverse image via `mapDerivedCategoryPlusHomologyFunctorIso`.
Global sections are invariant under inverse image along eA.hom: use the invertible
adjunction unit and `lowerStarCompGlobalSectionsIso`. Therefore the canonical factor
is invertible on global homology by step 1; every other factor is the functorial
image of an isomorphism. Their composite is invertible. This works in every integer
degree, for zero complexes and for empty total spaces, without a torsion hypothesis. -/
theorem isIso_strictHenselization_baseChange_modelGlobalHomology
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (eA : Spec (.of A) ≅ strictLocalization s)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictLocalizationToBase s))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIso ((Sheaf.Γ (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K))) := by
  have hcanonical := isIso_globalHomology_of_mate AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback f (strictLocalizationToBase s)).toCommSq K n
    (isIso_strictHenselization_baseChange_globalHomology f s K n)
  exact isIso_globalHomology_isoModel AddCommGrpCat.{u + 1} f
    (strictLocalizationToBase s)
    (pullback.fst f (strictLocalizationToBase s))
    (pullback.snd f (strictLocalizationToBase s))
    (IsPullback.of_hasPullback f (strictLocalizationToBase s)) eA p₀ f₀ sq₀ K n

end AlgebraicGeometry.Etale
