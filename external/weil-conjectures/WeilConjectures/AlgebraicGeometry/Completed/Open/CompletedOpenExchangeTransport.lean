/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Completed open exchange on the shared pullback presentation

Source: blueprint order 1587; Stacks Tags 03DI, 09BP and 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).

The old open exchange is retained. Its transport to `d.completedPull` is induced
by the actual coefficient maps and universal derived counits on strict towers.
The completion-unit equation retains its ordinary adjoint-mate normalization.

## Main definitions

- `cbcDatumCompletedTransport`: the normalized comparison of pullback presentations.
- `cbcDatumCompletedExchange`: completed open exchange on `d.completedPull`.

## Main statements

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
private theorem exactDerivedCounitComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : L ≅ F.mapDerivedCategory, ∀ P : CochainComplex C ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let e := CategoryTheory.Functor.leftDerivedUnique F.mapDerivedCategory L ε
    F.mapDerivedCategoryFactorsh.hom W
  have hc (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε P := by
    have he := CategoryTheory.Functor.leftDerivedNatTrans_app L F.mapDerivedCategory ε
      F.mapDerivedCategoryFactorsh.hom W (𝟙 _)
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso C).inv.app P)
    dsimp at hn
    simp only [NatTrans.id_app, Category.comp_id] at he
    change e.hom.app _ ≫ _ = _ at he
    simp only [CategoryTheory.Functor.leftDerivedCounitOnComplex]
    rw [← he, F.mapDerivedCategoryFactorsh_hom_app]
    simp only [← Category.assoc]
    rw [hn]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    simp
  refine ⟨e, hc, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hp : e'.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) =
      e.hom.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)) := by
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage K))).1
    rw [he', hc]
  apply (cancel_epi (L.map (DerivedCategory.Q.objObjPreimageIso K).hom)).1
  rw [e'.hom.naturality, e.hom.naturality, hp]

/-- Counit normalization for an exact presentation of a left-derived functor.
Naming the entire condition keeps the concrete module-category presentations out of
repeated elaborations of the choice predicate.
Source: Stacks 05S7, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison). -/
def CategoryTheory.Functor.ExactDerivedCounitNormalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [hLim : PreservesFiniteLimits G] [hColim : PreservesFiniteColimits G]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory) : Prop :=
  ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P =
    ε P ≫ DerivedCategory.Q.map (eqToIso (hp P)).hom

private theorem exactDerivedCounitTransport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (he : F = G)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (hp : ∀ P : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P) :
    ∃! e : L ≅ G.mapDerivedCategory,
      ExactDerivedCounitNormalization F G L
        (CategoryTheory.Functor.leftDerivedCounitOnComplex F L ε) hp e := by
  cases he
  simpa only [ExactDerivedCounitNormalization, eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id,
    Category.comp_id] using exactDerivedCounitComparison F L ε

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance exactTowerFiniteLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

private instance exactTowerFiniteColimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

private theorem constantComplex_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (P : CochainComplex C ℤ) :
    ((Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj
        (((Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C).mapHomologicalComplex (.up ℤ)).obj P) := by
  refine HomologicalComplex.ext ?_ ?_
  · funext q
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro n m f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (F.map_id (P.X q)).symm
  · intro i j _
    ext n
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl

private theorem exactConstantComparison
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  exact Functor.exactSquare_fac e P

private theorem exactSquare_symm
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private def constantDerivedSquare
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)

private theorem constantDerivedSquare_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C) ⋙
      (Functor.whiskeringRight ℕᵒᵖ C D).obj F ≅
        F ⋙ (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D))
    (he : e = (Functor.compConstIso ℕᵒᵖ F).symm) :
    constantDerivedSquare F = (Functor.mapDerivedCategorySquareIso e).symm := by
  subst e
  apply Iso.ext
  exact exactSquare_symm (Functor.compConstIso ℕᵒᵖ F).symm

private def transportedSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (et : T ≅ T') (c : L' ⋙ DD ≅ DC ⋙ T') : L ⋙ DD ≅ DC ⋙ T :=
  isoWhiskerRight e DD ≪≫ c ≪≫ isoWhiskerLeft DC et.symm

attribute [local irreducible] constantDerivedSquare transportedSquare

private theorem transportConstantComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hCt : HasDerivedCategory (ℕᵒᵖ ⥤ C)] [hDt : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F G : C ⥤ D) [hF : F.Additive] [hG : G.Additive]
    [hLim : PreservesFiniteLimits G] [hColim : PreservesFiniteColimits G] (he : F = G)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory (ℕᵒᵖ ⥤ D))
    (ε : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (τ : ∀ P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ, Lt.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj P))
    (hp : ∀ P : CochainComplex C ℤ, (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P)
    (hpt : ∀ P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex (.up ℤ)).obj P =
        (((Functor.whiskeringRight ℕᵒᵖ C D).obj G).mapHomologicalComplex (.up ℤ)).obj P)
    (e : L ≅ G.mapDerivedCategory)
    (E : Lt ≅ ((Functor.whiskeringRight ℕᵒᵖ C D).obj G).mapDerivedCategory)
    (hn : ExactDerivedCounitNormalization F G L ε hp e)
    (ht : ExactDerivedCounitNormalization
      ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ C D).obj G) Lt τ hpt E)
    (P : CochainComplex C ℤ) :
    let Ct := (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C)
    let Dt := (Functor.const ℕᵒᵖ : D ⥤ ℕᵒᵖ ⥤ D)
    let c := constantDerivedSquare G
    let b := transportedSquare Ct.mapDerivedCategory Dt.mapDerivedCategory e E c
    Dt.mapDerivedCategory.map (ε P) ≫
        Dt.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eqToHom (constantComplex_eq F P)) =
      b.hom.app (DerivedCategory.Q.obj P) ≫
        Lt.map (Ct.mapDerivedCategoryFactors.hom.app P) ≫
        τ ((Ct.mapHomologicalComplex (.up ℤ)).obj P) := by
  -- Equality of the ordinary functors also identifies every strict transition.
  simp only [ExactDerivedCounitNormalization] at hn ht
  cases he
  simp only [eqToIso_refl, Iso.refl_hom] at hn ht
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn ht
  have hq :
      ((NatTrans.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F).hom (.up ℤ)).app P) =
        eqToHom (constantComplex_eq F P) := by
    ext q n
    simp only [HomologicalComplex.eqToHom_f, eqToHom_app, eqToHom_refl]
    rfl
  dsimp only
  simp only [transportedSquare, constantDerivedSquare, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Category.assoc]
  erw [← E.inv.naturality_assoc]
  erw [← ht, Iso.inv_hom_id_app_assoc]
  have hs := exactConstantComparison (Functor.compConstIso ℕᵒᵖ F) P
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hs
  erw [hs]
  erw [← Functor.map_comp_assoc, hn, hq]

private theorem transportedComparison_cancel
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (E : T ≅ T') (c : L' ⋙ DD ≅ DC ⋙ T') (K : C) :
    (transportedSquare DC DD e E c).hom.app K ≫
        E.hom.app (DC.obj K) = DD.map (e.hom.app K) ≫ c.hom.app K := by
  simp only [transportedSquare, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem transportedComparison_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L L' : C ⥤ D} {T T' : E ⥤ F} (DC : C ⥤ E) (DD : D ⥤ F)
    (e : L ≅ L') (et : T ≅ T') (c c' : L' ⋙ DD ≅ DC ⋙ T')
    (c₀ : L ⋙ DD ≅ DC ⋙ T) (hc : c = c')
    (hb : transportedSquare DC DD e et c = c₀) (K : C) :
    c₀.hom.app K ≫ et.hom.app (DC.obj K) =
      DD.map (e.hom.app K) ≫ c'.hom.app K := by
  subst c₀
  subst c'
  exact transportedComparison_cancel DC DD e et c K

private theorem completedUnitTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (CT : C ⥤ E) (CS : D ⥤ F) (Q : C ⥤ E) (R : F ⥤ D)
    (L L' : C ⥤ D) (T T' : E ⥤ F) (e : L ≅ L') (et : T ≅ T')
    (c₁ : L ⋙ CS ≅ CT ⋙ T) (c₂ : L' ⋙ CS ≅ CT ⋙ T')
    (η η' : 𝟭 D ⟶ CS ⋙ R) (hη : η = η') (α : CT ⟶ Q)
    (hc : ∀ K, c₁.hom.app K ≫ et.hom.app (CT.obj K) =
      CS.map (e.hom.app K) ≫ c₂.hom.app K) (K : C) :
    (η.app (L.obj K) ≫ R.map (c₁.hom.app K ≫ T.map (α.app K))) ≫
        R.map (et.hom.app (Q.obj K)) =
      e.hom.app K ≫ η'.app (L'.obj K) ≫ R.map (c₂.hom.app K ≫ T'.map (α.app K)) := by
  cases hη
  have hs : c₁.hom.app K ≫ T.map (α.app K) ≫ et.hom.app (Q.obj K) =
      CS.map (e.hom.app K) ≫ c₂.hom.app K ≫ T'.map (α.app K) := by
    rw [et.hom.naturality, ← Category.assoc, hc, Category.assoc]
  have hu := η.naturality (e.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  calc
    _ = η.app (L.obj K) ≫ R.map
        (c₁.hom.app K ≫ T.map (α.app K) ≫ et.hom.app (Q.obj K)) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = η.app (L.obj K) ≫ R.map
        (CS.map (e.hom.app K) ≫ c₂.hom.app K ≫ T'.map (α.app K)) := by rw [hs]
    _ = _ := by
      rw [Functor.map_comp, ← Category.assoc, ← hu, Category.assoc]

private theorem exactLeftDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (P : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app P) := by
  have hh := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at hh
  rw [F.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  apply (cancel_mono (G.rightDerivedFunctor.map
    (F.mapDerivedCategoryFactors.hom.app P))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [G.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at hh
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hh
  exact hh

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits
attribute [local irreducible] constantDerivedSquare transportedSquare

namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {S T : Scheme.{t}} (h : S ⟶ T)

private theorem constantRlimUnit_eq (V : Scheme.{t}) :
    completedConstantRlimUnit d V = (d.constantRlimAdjunction V).unit := by
  apply (completedConstantRlimUnit_exists d V).unique
    (completedConstantRlimUnit_exists d V).exists.choose_spec
  intro P
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact exactLeftDerivedUnit (completedTowerConstant d V) lim constLimAdj P

private instance cbcOrdinaryUniversal :
    (completedOrdinaryPullback h d).IsLeftDerivedFunctor
      (completedOrdinaryPullbackCounit h d)
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ)) := by
  unfold completedOrdinaryPullback completedOrdinaryPullbackCounit
  exact (completedOrdinaryPullback_exists h d).choose_spec.choose_spec.1

private instance cbcTowerUniversal :
    (completedTowerPullback h d).IsLeftDerivedFunctor
      (completedTowerPullbackCounit h d)
      (HomotopyCategory.quasiIso (pbcTowers T (pbcAdicCompletion T d)) (.up ℤ)) := by
  unfold completedTowerPullback completedTowerPullbackCounit
  exact (completedTowerPullback_exists h d).choose_spec.choose_spec.1

/-- Both finite coefficient maps are induced by the same constant-section map.
Source: Stacks 099N, finite reductions (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand finiteRingIso and completedFiniteCoefficientMap. Their outer maps
are the same constant/function comparisons, and their middle map is the same
constant inverse-image comparison. Thus their composites agree. -/
theorem cbcDatumFiniteCoefficient_eq (n : ℕ) :
    completedFiniteCoefficientMap h d n = (d.finiteRingIso h n).hom := by
  rfl

/-- The completed scalar structures coincide, with every quotient projection retained.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: both maps are limit lifts. After the n-th projection they are inverse
image of that projection followed by the finite map of cbcDatumFiniteCoefficient_eq.
Joint monicity of the limit projections gives equality. Naturality in every
quotient transition is the finite constant-comparison naturality square. -/
theorem cbcDatumCoefficient_eq :
    completedCoefficientMap h d = (d.integralRingIso h).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap h d ≫ d.projection S n.unop =
    (d.integralRingIso h).hom ≫ d.projection S n.unop
  calc
    _ = completedCoefficientComponent h d n.unop :=
      limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      exact congrArg ((proEtaleSheafInverseImage h CommRingCat).map
        (d.projection T n.unop) ≫ ·) (cbcDatumFiniteCoefficient_eq d h n.unop)

/-- Both ordinary functors use identical inverse image and sheafified tensor data.
Source: Stacks 03EK, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: use cbcDatumCoefficient_eq. The recorded scalar-extension object formula
identifies every object with changeOfRings; its recorded map formula identifies
every map with changeOfRingsHom after the object equality transports. Functor
extensionality gives the equality. These formulas fix the tensor unit 1 tensor x. -/
theorem cbcDatumModulePull_eq :
    completedModulePullback h d =
      proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h) := by
  unfold completedModulePullback
  rw [cbcDatumCoefficient_eq]
  apply CategoryTheory.Functor.ext
  · intro M N f
    exact (completedAdicChangeData S (d.integralRingIso h).hom).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage h (d.completedRing T)).map f)

/-- Strict tower functors agree on levels AND transition maps.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: whisker cbcDatumModulePull_eq by the identity on the entire strict tower
category. Both constructions apply that module functor to every transition,
including the actual quotient maps of the reduction tower. -/
theorem cbcDatumTowerModulePull_eq :
    completedTowerModulePullback h d = d.towerModulePull h := by
  exact congrArg ((Functor.whiskeringRight ℕᵒᵖ _ _).obj) (cbcDatumModulePull_eq d h)

/-- The module comparison on actual complexes, with the additive structures installed.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: substitute cbcDatumModulePull_eq; preservation of zero morphisms is a
proposition, so its two instance witnesses coincide. The mapped complexes agree. -/
theorem cbcDatumModulePullComplex_eq
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj P =
      ((proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h)).mapHomologicalComplex (.up ℤ)).obj P := by
  have aux (F G : pbcModules T (pbcAdicCompletion T d) ⥤
      pbcModules S (pbcAdicCompletion S d))
      [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (he : F = G) :
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P := by
    cases he
    rfl
  exact aux _ _ (cbcDatumModulePull_eq d h)

/-- The strict comparison on complexes keeps all levels and transitions.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: substitute cbcDatumTowerModulePull_eq. The zero-preservation witnesses
are proof irrelevant, so the mapped strict tower complexes agree. -/
theorem cbcDatumTowerPullComplex_eq
    (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) :
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).obj P =
      ((d.towerModulePull h).mapHomologicalComplex (.up ℤ)).obj P := by
  have aux (F G : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcTowers S (pbcAdicCompletion S d))
      [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (he : F = G) :
      (F.mapHomologicalComplex (.up ℤ)).obj P =
        (G.mapHomologicalComplex (.up ℤ)).obj P := by
    cases he
    rfl
  exact aux _ _ (cbcDatumTowerModulePull_eq d h)

/-- The ordinary derived comparison is uniquely fixed by its resolving counit.
Source: Stacks 099N, 06YS (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the ordinary functors coincide by cbcDatumModulePull_eq. The datum
presentation is exact, so its termwise factorization is a universal left-derived
counit. Uniqueness of the universal derived pair gives the isomorphism and the
displayed counit equation on complexes. Resolve by K-flat complexes to prove
uniqueness; exactness extends the equation to every representative. -/
theorem cbcDatumOrdinaryTransport_exists :
    ∃! e : completedOrdinaryPullback h d ≅ d.pull h,
      ExactDerivedCounitNormalization (completedModulePullback h d)
        (proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h)) (completedOrdinaryPullback h d)
        (completedOrdinaryPullbackComplexCounit h d)
        (cbcDatumModulePullComplex_eq d h) e := by
  exact exactDerivedCounitTransport (completedModulePullback h d)
    (proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
      (d.integralRingIso h)) (cbcDatumModulePull_eq d h)
    (completedOrdinaryPullback h d) (completedOrdinaryPullbackCounit h d)
    (cbcDatumModulePullComplex_eq d h)

/-- Ordinary pullback transport with its universal-counit normalization.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumOrdinaryTransport : completedOrdinaryPullback h d ≅ d.pull h :=
  (cbcDatumOrdinaryTransport_exists d h).exists.choose

/-- The strict derived tower comparison retains the universal resolving counit.
Source: Stacks 099N, 06YS (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: cbcDatumTowerModulePull_eq identifies the whole ordinary tower functor.
Its exact termwise derived functor and the objectwise K-flat derived construction
are universal left-derived pairs. Their unique comparison satisfies the equation
below. In particular it compares one strict tower, including transitions, rather
than choosing independent isomorphisms of its finite evaluations. -/
theorem cbcDatumTowerTransport_exists :
    ∃! e : completedTowerPullback h d ≅ d.towerPull h,
      ExactDerivedCounitNormalization
        (hLim := (d.towerModulePull_exact h).1)
        (hColim := (d.towerModulePull_exact h).2)
        (completedTowerModulePullback h d)
        (d.towerModulePull h) (completedTowerPullback h d)
        (completedTowerPullbackComplexCounit h d)
        (cbcDatumTowerPullComplex_eq d h) e := by
  have : PreservesFiniteLimits (d.towerModulePull h) :=
    (d.towerModulePull_exact h).1
  have : PreservesFiniteColimits (d.towerModulePull h) :=
    (d.towerModulePull_exact h).2
  exact exactDerivedCounitTransport (completedTowerModulePullback h d)
    (d.towerModulePull h) (cbcDatumTowerModulePull_eq d h)
    (completedTowerPullback h d) (completedTowerPullbackCounit h d)
    (cbcDatumTowerPullComplex_eq d h)

/-- Canonical comparison of derived strict tower pullback presentations.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumTowerTransport : completedTowerPullback h d ≅ d.towerPull h :=
  (cbcDatumTowerTransport_exists d h).exists.choose

/-- Apply Rlim to the strict tower transport of the very same reduction functor.
The inverse-limit functors in the two interfaces are definitionally identical.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumCompletedTransport : cbcCompletedPullback d h ≅ d.completedPull h :=
  isoWhiskerLeft (completedReductionTower T d)
    (isoWhiskerRight (cbcDatumTowerTransport d h) (completedTowerRlim d S))

/-- The current recorded strict completed pullback has the same normalized transport.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
abbrev cbcDatumActualStrictTransport :
    pbcActualStrictCompletedPull d h ≅ d.completedPull h :=
  cbcDatumCompletedTransport d h

private theorem datumConstantComparison (K : d.derived T) :
    (completedPullbackConstantIso h d).hom.app K ≫
        (cbcDatumTowerTransport d h).hom.app ((completedDerivedConstant d T).obj K) =
      (completedDerivedConstant d S).map ((cbcDatumOrdinaryTransport d h).hom.app K) ≫
        (d.derivedConstantPullbackIso h).inv.app K := by
  let F := proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
    (d.integralRingIso h)
  let c : d.pull h ⋙ completedDerivedConstant d S ≅
      completedDerivedConstant d T ⋙ d.towerPull h :=
    constantDerivedSquare
      (C := pbcModules T (pbcAdicCompletion T d))
      (D := pbcModules S (pbcAdicCompletion S d))
      (hC := proEtaleRingModules_hasDerivedCategory T (pbcAdicCompletion T d))
      (hD := proEtaleRingModules_hasDerivedCategory S (pbcAdicCompletion S d))
      (hCt := pbcTowers_hasDerivedCategory T (pbcAdicCompletion T d))
      (hDt := pbcTowers_hasDerivedCategory S (pbcAdicCompletion S d)) F
  have hc : c = (d.derivedConstantPullbackIso h).symm := by
    have hi : d.constantPullbackIso h = (Functor.compConstIso ℕᵒᵖ F).symm := by
      ext M n
      rfl
    have hframe : c = constantDerivedSquare F := by rfl
    exact hframe.trans (constantDerivedSquare_eq F (d.constantPullbackIso h) hi)
  let b : completedOrdinaryPullback h d ⋙ completedDerivedConstant d S ≅
      completedDerivedConstant d T ⋙ completedTowerPullback h d :=
    transportedSquare (completedDerivedConstant d T) (completedDerivedConstant d S)
      (cbcDatumOrdinaryTransport d h) (cbcDatumTowerTransport d h) c
  have hb : HasCompletedPullbackConstantNormalization h d b := by
    intro P _
    have hp := transportConstantComparison
      (C := pbcModules T (pbcAdicCompletion T d))
      (D := pbcModules S (pbcAdicCompletion S d))
      (hC := proEtaleRingModules_hasDerivedCategory T (pbcAdicCompletion T d))
      (hD := proEtaleRingModules_hasDerivedCategory S (pbcAdicCompletion S d))
      (hCt := pbcTowers_hasDerivedCategory T (pbcAdicCompletion T d))
      (hDt := pbcTowers_hasDerivedCategory S (pbcAdicCompletion S d))
      (hF := completedModulePullback_additive h d)
      (hG := proEtaleRingModulePullback_additive h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h))
      (hLim := proEtaleRingModulePullback_preservesFiniteLimits h
        (d.completedRing T) (d.completedRing S) (d.integralRingIso h))
      (hColim := proEtaleRingModulePullback_preservesFiniteColimits h
        (d.completedRing T) (d.completedRing S) (d.integralRingIso h))
      (completedModulePullback h d) F
      (cbcDatumModulePull_eq d h) (completedOrdinaryPullback h d) (completedTowerPullback h d)
      (completedOrdinaryPullbackComplexCounit h d) (completedTowerPullbackComplexCounit h d)
      (cbcDatumModulePullComplex_eq d h) (cbcDatumTowerPullComplex_eq d h)
      (cbcDatumOrdinaryTransport d h) (cbcDatumTowerTransport d h)
      (cbcDatumOrdinaryTransport_exists d h).exists.choose_spec
      (cbcDatumTowerTransport_exists d h).exists.choose_spec P
    exact hp
  -- This is equality in the strict derived tower category; evaluating separate
  -- levels would not determine the comparison.
  have he : b = completedPullbackConstantIso h d :=
    (completedPullbackConstantIso_exists h d).unique hb
      (completedPullbackConstantIso_exists h d).exists.choose_spec
  exact transportedComparison_eq (completedDerivedConstant d T)
    (completedDerivedConstant d S) (cbcDatumOrdinaryTransport d h)
    (cbcDatumTowerTransport d h) c (d.derivedConstantPullbackIso h).symm
    (completedPullbackConstantIso h d) hc he K

/-- The transport preserves the actual ordinary-to-completed quotient unit.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand both units into constant-tower/Rlim unit, constant-pullback
comparison and strict quotient augmentation. The constant-tower comparisons
are fixed by the same ordinary and tower counits. The quotient augmentation
sends x to 1 tensor x on both sides by cbcDatumModulePull_eq. The constant-limit
adjunction is fixed by compatible-family projections, so its unit agrees too.
Naturality and the derived counit equations then give the displayed identity.
This argument retains all quotient transitions and applies to ambient inputs. -/
theorem cbcDatumCompletedTransport_unit (K : d.derived T) :
    (cbcCompletedPullbackComparison d h).app K ≫
        (cbcDatumCompletedTransport d h).hom.app K =
      (cbcDatumOrdinaryTransport d h).hom.app K ≫ d.ordinaryToCompleted h K := by
  have hu := completedUnitTransport
    (completedDerivedConstant d T) (completedDerivedConstant d S)
    (completedReductionTower T d) (completedTowerRlim d S)
    (completedOrdinaryPullback h d) (d.pull h)
    (completedTowerPullback h d) (d.towerPull h)
    (cbcDatumOrdinaryTransport d h) (cbcDatumTowerTransport d h)
    (completedPullbackConstantIso h d) (d.derivedConstantPullbackIso h).symm
    (completedConstantRlimUnit d S) (d.constantRlimAdjunction S).unit
    (constantRlimUnit_eq d S) (completedReductionTowerUnit d T)
    (datumConstantComparison d h) K
  change completedPullbackComparison h d K ≫
      (completedTowerRlim d S).map
        ((cbcDatumTowerTransport d h).hom.app ((completedReductionTower T d).obj K)) = _
  dsimp only [completedPullbackComparison, AdicCoefficientDatum.ordinaryToCompleted]
  exact hu

/-- The currently recorded strict-tower unit obeys the same normalization.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand pbcActualStrictCompletedPullUnit and the old comparison. Both are
the same constant-tower unit followed by the same normalized constant-pullback
comparison and the same strict quotient augmentation. Functor associativity
identifies their components. Apply cbcDatumCompletedTransport_unit. -/
theorem cbcDatumActualStrictTransport_unit (K : d.derived T) :
    (pbcActualStrictCompletedPullUnit d h).app K ≫
        (cbcDatumActualStrictTransport d h).hom.app K =
      (cbcDatumOrdinaryTransport d h).hom.app K ≫ d.ordinaryToCompleted h K := by
  simpa only [pbcActualStrictCompletedPullUnit, cbcCompletedPullbackComparison,
    completedPullbackComparison, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Functor.map_comp] using
      cbcDatumCompletedTransport_unit d h K

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

/-- Ordinary exchange transported with the universal counits; hence it is the
same generator-normalized adjoint mate as the retained ordinary exchange.
Source: Stacks 03DI, 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumOrdinaryExchange :
    cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ d.pull g ⟶
      d.pull gU ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  whiskerLeft (cbcDerivedOpenShriek d j sq.isOpenImmersion)
      (cbcDatumOrdinaryTransport d g).inv ≫
    cbcOrdinaryExchange d sq ≫
      whiskerRight (cbcDatumOrdinaryTransport d gU).hom
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion')

/-- Canonical completed open exchange on the same presentation as proper exchange.
It is Rlim of the finite exchange followed by the extension/Rlim comparison,
transported through the strict tower counits, with no new endpoint choice.
Source: Stacks 09BP, 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ d.completedPull g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ d.completedPull gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  whiskerLeft ((cbcCompleteProperty d U r a ha).ι ⋙
      cbcDerivedOpenShriek d j sq.isOpenImmersion)
      (cbcDatumCompletedTransport d g).inv ≫
    cbcCompletedExchange d sq r a ha ≫
      whiskerLeft (cbcCompleteProperty d U r a ha).ι
        (whiskerRight (cbcDatumCompletedTransport d gU).hom
          (cbcDerivedOpenShriek d j' sq.isOpenImmersion'))


/-- Quasi-compact open extension preserves intrinsic completeness, and its canonical
completed exchange is invertible and natural, with both sides intrinsically complete.
Source: blueprint order 1587; Stacks 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof:
1. Use lem-weil-proetale-weakly-etale-localization and sectionwise module limits
to identify completed rings on both slices by every finite projection.
lem-pc-quasi-compact-base-change makes the second open quasi-compact.
2. lem-pur-site-restriction-module-adjunction-exact gives exact sheafified
extension and restriction; situation-conventions descends
them termwise. Scalar restriction leaves the direct-sum summands unchanged.
3. lem-pc-kflat-resolution and lem-weil-pbc-ringed-slice-extension-tensor show
that extension preserves K-flat complexes and identifies strict reductions,
including every quotient transition, by the same pure tensor formula.
4. lem-weil-pbc-proetale-ringed-open-closed expresses extension as a kernel of
product-preserving functors. Closed inverse image preserves products by
lem-weil-pbc-proetale-immersion-limit-preservation, including the empty product.
5. Exact countable products and lem-weil-derived-limit-products-core give the
functorial signed Roos fiber. prop-weil-pbc-rlim-functoriality and
lem-weil-derived-limit-roos-complex identify it with the specified Rlim.
Extension commutes with its two products and structure maps, as required by
lem-cbc-exact-functor-rlim and the ringed strict tower homotopy-limit lemma.
6. Apply that comparison to the finite-free Koszul tower and its unit from
def-weil-pbc-intrinsic-completion to preserve completeness. Use
lemma-weil-pbc-completed-pullback-reduction for completeness of pullback.
7. prop-weil-pbc-proetale-constant-exact and
proposition-extension-zero-restriction-closed-subscheme--11 give finite adjoint-mate exchanges.
The summand and scalar-restriction formulas and site-morphism composition show
they commute with quotient transitions. Constant/completed finite comparisons
from lem-weil-pbc-constant-completion-equivalence retain those transitions.
8. Apply functorial Rlim to that strict tower exchange and the inverse
extension/Rlim comparison. This is the old canonical completed exchange.
Transport it by cbcDatumCompletedTransport, which retains coefficients,
transitions, resolving counits and quotient units. Its mate normalization is
cbcDatumCompletedExchange_unit. Completeness is invariant under these
isomorphisms; the two applications of step 6 give the displayed complete
endpoints. All constituents are natural, so their composite is natural. -/
theorem completedOpenExchangeComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcDatumCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((d.completedPull g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((d.completedPull gU).obj K.obj))) := by
  have hold := completedExtensionZeroComparison d sq r a ha
  have : IsIso (cbcCompletedExchange d sq r a ha) := hold.1
  constructor
  · unfold cbcDatumCompletedExchange
    infer_instance
  · have hpull {V W : Scheme.{t}} (f : V ⟶ W) (M : d.derived W)
        (hm : cbcCompleteProperty d W r a ha M) :
        cbcCompleteProperty d V r a ha ((d.completedPull f).obj M) := by
      let N := (d.completedPull f).obj M
      let C := DerivedCategory.Q.objPreimage N
      let eN : DerivedCategory.Q.obj C ≅ N := DerivedCategory.Q.objObjPreimageIso N
      let e := eN ≪≫ ((cbcDatumCompletedTransport d f).app M).symm
      have hc := (completedPullback_reduction f d r a ha M
        (DerivedCategory.Q.objPreimage M) (DerivedCategory.Q.objObjPreimageIso M) hm).1 C e
      change IsIso (e.inv ≫ DerivedCategory.Q.map
        (intrinsicCompletionComplexUnit V d r a C)) at hc
      have : IsIso (DerivedCategory.Q.map
          (intrinsicCompletionComplexUnit V d r a C)) :=
        IsIso.of_isIso_comp_left e.inv _
      change IsIso (eN.inv ≫ DerivedCategory.Q.map
        (intrinsicCompletionComplexUnit V d r a C))
      infer_instance
    have hsq : IsPullback gU j' j g :=
      IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
    have : QuasiCompact j' := MorphismProperty.of_isPullback (P := @QuasiCompact)
      hsq inferInstance
    let hi := IsPullback.id_horiz j'
    let sq' : AlgebraicGeometry.OpenImmersionSquare (𝟙 U') j' j' (𝟙 X') :=
      { toCommSq := hi.toCommSq
        isoPullback := hi.isoPullback
        hom_fst := hi.isoPullback_hom_fst
        hom_snd := hi.isoPullback_hom_snd
        isOpenImmersion := sq.isOpenImmersion'
        isOpenImmersion' := sq.isOpenImmersion' }
    intro K
    refine ⟨(hold.2 K).1, hpull g _ (hold.2 K).1, ?_⟩
    exact ((completedExtensionZeroComparison d sq' r a ha).2
      ⟨(d.completedPull gU).obj K.obj, hpull gU K.obj K.property⟩).1


end AlgebraicGeometry.Scheme
