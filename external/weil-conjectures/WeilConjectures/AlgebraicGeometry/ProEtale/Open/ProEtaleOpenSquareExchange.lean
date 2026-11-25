/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Canonical open-square exchange on the small pro-etale site

All functors act on the intrinsic constant-ring module categories.
The comparison is fixed as the inverse of the open-adjunction mate; the data below
include restriction normalization, both identity laws and both pasting laws.

## References

* Stacks, Tags 03DI and 00YV
* Stacks, Tag 05RU
* Stacks, Section 0735
* Stacks, Tags 03S6 and 04J0
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

-- Use the equivalence API without expanding the concrete realization equivalence.
attribute [local irreducible] sfIntrinsicModuleEquivalence

/-- The open adjunction transported through the canonical realization equivalences. -/
noncomputable def sfIntrinsicOpenAdjunction {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : sfIntrinsicExtensionByZero j A ⊣ sfIntrinsicPullback A j :=
  ((sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
    (sfIntrinsicModuleEquivalence Y A).toAdjunction

/-- Composition of open extensions is the unique comparison respecting composite units. -/
noncomputable def sfIntrinsicOpenComp {V U Y : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    sfIntrinsicExtensionByZero (i ≫ j) A ≅
      sfIntrinsicExtensionByZero i A ⋙ sfIntrinsicExtensionByZero j A :=
  (((sfIntrinsicOpenAdjunction A i).comp (sfIntrinsicOpenAdjunction A j)).ofNatIsoRight
    (sfIntrinsicPullbackComp A i j).symm).leftAdjointUniq
      (sfIntrinsicOpenAdjunction A (i ≫ j)) |>.symm

/-- Identity open extension, normalized by its adjunction unit. -/
noncomputable def sfIntrinsicOpenId (Y : Scheme.{u}) :
    sfIntrinsicExtensionByZero (𝟙 Y) A ≅ 𝟭 _ :=
  ((sfIntrinsicOpenAdjunction A (𝟙 Y)).ofNatIsoRight
    (sfIntrinsicPullbackId A Y)).leftAdjointUniq Adjunction.id

/-- Commuting pullbacks for a commutative square, with the canonical coefficient action. -/
noncomputable def sfIntrinsicSquarePullback {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicPullback A j ⋙ sfIntrinsicPullback A gU ≅
      sfIntrinsicPullback A g ⋙ sfIntrinsicPullback A j' :=
  (sfIntrinsicPullbackComp A gU j).symm ≪≫
    eqToIso (congrArg (sfIntrinsicPullback A) w) ≪≫ sfIntrinsicPullbackComp A j' g

/-- The reverse exchange map is the mate of the pullback square. Explicitly it applies
`j'_!` to `g_U^*` of the open unit, then the pullback-square comparison, and finally the
open counit. Thus it is a specified map, rather than a freely chosen isomorphism. -/
noncomputable def sfIntrinsicOpenMate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicPullback A gU ⋙ sfIntrinsicExtensionByZero j' A ⟶
      sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A g :=
  whiskerRight (whiskerRight (sfIntrinsicOpenAdjunction A j).unit
    (sfIntrinsicPullback A gU)) (sfIntrinsicExtensionByZero j' A) ≫
  whiskerRight (whiskerLeft (sfIntrinsicExtensionByZero j A)
    (sfIntrinsicSquarePullback A gU j' j g w).hom) (sfIntrinsicExtensionByZero j' A) ≫
  whiskerLeft (sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A g)
    (sfIntrinsicOpenAdjunction A j').counit

/-- Exact extension by zero on the full, unbounded intrinsic derived category. -/
noncomputable abbrev sfIntrinsicDerivedOpen {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero j A).mapDerivedCategory

/-- Descend an actual natural transformation of exact intrinsic functors termwise. -/
noncomputable def sfIntrinsicDeriveMap {X Y : Scheme.{u}}
    {F G : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A)}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (whiskerRight (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The specified derived reverse exchange is the exact termwise descent of the open mate. -/
noncomputable def sfIntrinsicDerivedOpenMate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j' ⟶
      sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g :=
  (mapDerivedCategoryCompIso (sfIntrinsicPullback A gU)
    (sfIntrinsicExtensionByZero j' A)).hom ≫
  sfIntrinsicDeriveMap A (sfIntrinsicOpenMate A gU j' j g w) ≫
  (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero j A)
    (sfIntrinsicPullback A g)).inv

/-- The derived open unit, with the localization identity and composition comparisons. -/
noncomputable def sfIntrinsicDerivedOpenUnit {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : 𝟭 (proEtaleDerivedCategory U A) ⟶
      sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A j :=
  (mapDerivedCategoryIdIso _).inv ≫
    sfIntrinsicDeriveMap A (sfIntrinsicOpenAdjunction A j).unit ≫
    (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero j A)
      (sfIntrinsicPullback A j)).inv

/-- Pullback composition on unbounded derived categories. -/
noncomputable def sfIntrinsicDerivedPullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sfIntrinsicDerivedPullback A (f ≫ g) ≅
      sfIntrinsicDerivedPullback A g ⋙ sfIntrinsicDerivedPullback A f :=
  mapDerivedCategoryNatIso (sfIntrinsicPullbackComp A f g) ≪≫
    (mapDerivedCategoryCompIso (sfIntrinsicPullback A g) (sfIntrinsicPullback A f)).symm

/-- Open-extension composition on unbounded derived categories. -/
noncomputable def sfIntrinsicDerivedOpenComp {V U Y : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    sfIntrinsicDerivedOpen A (i ≫ j) ≅ sfIntrinsicDerivedOpen A i ⋙ sfIntrinsicDerivedOpen A j :=
  mapDerivedCategoryNatIso (sfIntrinsicOpenComp A i j) ≪≫
    (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero i A)
      (sfIntrinsicExtensionByZero j A)).symm

/-- Identity pullback on the unbounded derived category. -/
noncomputable def sfIntrinsicDerivedPullbackId (Y : Scheme.{u}) :
    sfIntrinsicDerivedPullback A (𝟙 Y) ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso (sfIntrinsicPullbackId A Y) ≪≫ mapDerivedCategoryIdIso _

/-- Identity open extension on the unbounded derived category. -/
noncomputable def sfIntrinsicDerivedOpenId (Y : Scheme.{u}) :
    sfIntrinsicDerivedOpen A (𝟙 Y) ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso (sfIntrinsicOpenId A Y) ≪≫ mapDerivedCategoryIdIso _

/-- The derived pullback identification `j^* ⋙ gU^* ≅ g^* ⋙ j'^*` for a commutative square. -/
noncomputable def sfIntrinsicDerivedSquarePullback {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicDerivedPullback A j ⋙ sfIntrinsicDerivedPullback A gU ≅
      sfIntrinsicDerivedPullback A g ⋙ sfIntrinsicDerivedPullback A j' :=
  mapDerivedCategoryCompIso (sfIntrinsicPullback A j) (sfIntrinsicPullback A gU) ≪≫
    mapDerivedCategoryNatIso (sfIntrinsicSquarePullback A gU j' j g w) ≪≫
    (mapDerivedCategoryCompIso (sfIntrinsicPullback A g) (sfIntrinsicPullback A j')).symm

/-- A coherent family of the canonical exchange isomorphisms, whose inverses are the
open-adjunction mates, satisfying restriction normalization and the identity and pasting laws.
-/
structure SfOpenSquareExchangeData where
  exchange : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (_sq : IsPullback gU j' j g),
    sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
      sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j'
  canonical : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g),
    (exchange gU j' j g sq).inv = sfIntrinsicDerivedOpenMate A gU j' j g sq.w
  restriction : ∀ {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) (K : proEtaleDerivedCategory U A),
    (sfIntrinsicDerivedPullback A gU).map ((sfIntrinsicDerivedOpenUnit A j).app K) ≫
      (sfIntrinsicDerivedSquarePullback A gU j' j g sq.w).hom.app
        ((sfIntrinsicDerivedOpen A j).obj K) ≫
      (sfIntrinsicDerivedPullback A j').map ((exchange gU j' j g sq).hom.app K) =
        (sfIntrinsicDerivedOpenUnit A j').app ((sfIntrinsicDerivedPullback A gU).obj K)
  horizontal_id : ∀ {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U) j j (𝟙 Y)),
    (exchange (𝟙 U) j j (𝟙 Y) sq).hom =
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackId A Y)).hom ≫
      (isoWhiskerRight (sfIntrinsicDerivedPullbackId A U) (sfIntrinsicDerivedOpen A j)).inv
  vertical_id : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y)
    (sq : IsPullback g (𝟙 X) (𝟙 Y) g),
    (exchange g (𝟙 X) (𝟙 Y) g sq).hom =
      (isoWhiskerRight (sfIntrinsicDerivedOpenId A Y) (sfIntrinsicDerivedPullback A g)).hom ≫
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedOpenId A X)).inv
  horizontal_pasting : ∀ {U'' U' U Y'' Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (hU : U'' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y') (j'' : U'' ⟶ Y'')
    (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (sq : IsPullback gU j' j g) (sq' : IsPullback hU j'' j' h)
    (outer : IsPullback (hU ≫ gU) j'' j (h ≫ g)),
    (exchange (hU ≫ gU) j'' j (h ≫ g) outer).hom =
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j)
        (sfIntrinsicDerivedPullbackComp A h g)).hom ≫
      whiskerRight (exchange gU j' j g sq).hom (sfIntrinsicDerivedPullback A h) ≫
      whiskerLeft (sfIntrinsicDerivedPullback A gU) (exchange hU j'' j' h sq').hom ≫
      (isoWhiskerRight (sfIntrinsicDerivedPullbackComp A hU gU)
        (sfIntrinsicDerivedOpen A j'')).inv
  vertical_pasting : ∀ {V' V U' U Y' Y : Scheme.{u}}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (gV : V' ⟶ V) (gU : U' ⟶ U) (g : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion i'] [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) (sq' : IsPullback gV i' i gU)
    (outer : IsPullback gV (i' ≫ j') (i ≫ j) g),
    (exchange gV (i' ≫ j') (i ≫ j) g outer).hom =
      (isoWhiskerRight (sfIntrinsicDerivedOpenComp A i j)
        (sfIntrinsicDerivedPullback A g)).hom ≫
      whiskerLeft (sfIntrinsicDerivedOpen A i) (exchange gU j' j g sq).hom ≫
      whiskerRight (exchange gV i' i gU sq').hom (sfIntrinsicDerivedOpen A j') ≫
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A gV)
        (sfIntrinsicDerivedOpenComp A i' j')).inv

-- First prove transport and mate coherence with abstract categories.
section TransportCalculus

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

private def trFunctor (e : C₁ ≌ D₁) (f : C₂ ≌ D₂) (F : C₁ ⥤ C₂) : D₁ ⥤ D₂ :=
  e.inverse ⋙ F ⋙ f.functor

private def trIso (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G : C₁ ⥤ C₂} (a : F ≅ G) : trFunctor e f F ≅ trFunctor e f G :=
  isoWhiskerLeft e.inverse (isoWhiskerRight a f.functor)

private def trComp (e : C₁ ≌ D₁) (f : C₂ ≌ D₂) (g : C₃ ≌ D₃)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    trFunctor e g (F ⋙ G) ≅ trFunctor e f F ⋙ trFunctor f g G :=
  isoWhiskerLeft e.inverse (isoWhiskerRight
    (isoWhiskerLeft F (f.funInvIdAssoc G).symm) g.functor)

private theorem trIso_refl (e : C₁ ≌ D₁) (f : C₂ ≌ D₂) (F : C₁ ⥤ C₂) :
    trIso e f (Iso.refl F) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact f.functor.map_id _

private theorem trIso_trans (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G H : C₁ ⥤ C₂} (a : F ≅ G) (b : G ≅ H) :
    trIso e f (a ≪≫ b) = trIso e f a ≪≫ trIso e f b := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact f.functor.map_comp _ _

private theorem trIso_symm (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G : C₁ ⥤ C₂} (a : F ≅ G) :
    trIso e f a.symm = (trIso e f a).symm := rfl

private theorem trIso_path (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G H I : C₁ ⥤ C₂} {P Q : D₁ ⥤ D₂}
    (a : F ≅ G) (b : F ≅ H) (c : H ≅ I)
    (d : trFunctor e f G ≅ P) (k : trFunctor e f I ≅ Q) :
    (trIso e f a ≪≫ d).symm ≪≫ trIso e f b ≪≫ trIso e f c ≪≫ k =
      d.symm ≪≫ trIso e f (a.symm ≪≫ b ≪≫ c) ≪≫ k := by
  simp only [trIso_trans, trIso_symm, Iso.trans_symm, Iso.trans_assoc]

private def trNat (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G : C₁ ⥤ C₂} (a : F ⟶ G) : trFunctor e f F ⟶ trFunctor e f G :=
  whiskerLeft e.inverse (whiskerRight a f.functor)

private def trAdj (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R) :
    trFunctor e f L ⊣ trFunctor f e R :=
  (e.symm.toAdjunction.comp adj).comp f.toAdjunction

variable {C₄ D₄ : Type*} [Category C₄] [Category D₄]

private theorem rawMate_eq
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (G : C₁ ⥤ C₃) (H : C₂ ⥤ C₄)
    (a : R₁ ⋙ G ⟶ H ⋙ R₂) :
    ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ a)) =
      whiskerRight (whiskerRight adj₁.unit G) L₂ ≫
        whiskerRight (whiskerLeft L₁ a) L₂ ≫ whiskerLeft (L₁ ⋙ H) adj₂.counit := by
  apply NatTrans.ext
  funext X
  simp only [comp_obj, mateEquiv, Equiv.symm_mk, Equiv.coe_fn_mk, NatTrans.comp_app, id_obj,
    leftUnitor_inv_app, whiskerRight_app, Functor.comp_map, associator_inv_app,
    associator_hom_app, map_id, whiskerLeft_app, rightUnitor_hom_app, Category.comp_id,
    Category.id_comp, whiskerRight_twice, Category.assoc]

private theorem trMate (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄)
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (G : C₁ ⥤ C₃) (H : C₂ ⥤ C₄)
    (a : R₁ ⋙ G ⟶ H ⋙ R₂) :
    ((mateEquiv (trAdj e₁ e₂ adj₁) (trAdj e₃ e₄ adj₂)).symm
      (TwoSquare.mk _ _ _ _ ((trComp e₂ e₁ e₃ R₁ G).inv ≫ trNat e₂ e₃ a ≫
        (trComp e₂ e₄ e₃ H R₂).hom))) =
      (trComp e₁ e₃ e₄ G L₂).inv ≫
        trNat e₁ e₄ ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ a)) ≫
        (trComp e₁ e₂ e₄ L₁ H).hom := by
  apply NatTrans.ext
  funext X
  rw [rawMate_eq, rawMate_eq]
  simp only [trFunctor, comp_obj, trAdj, Equivalence.symm_functor, Equivalence.symm_inverse,
    whiskerRight_twice, trComp, Equivalence.funInvIdAssoc, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, isoWhiskerLeft_trans, isoWhiskerRight_trans, Iso.trans_inv,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, Iso.symm_inv, isoWhiskerRight_hom, Iso.symm_hom,
    Category.assoc, trNat, Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_comp, whiskerLeft_twice,
    Iso.hom_inv_id_assoc, whiskerRight_comp, NatTrans.comp_app, id_obj, associator_hom_app,
    whiskerRight_app, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    Equivalence.symm_unit, Functor.comp_map, map_comp, Equivalence.inv_fun_map,
    Iso.hom_inv_id_app_assoc, Equivalence.inverse_counitInv_comp_assoc, associator_inv_app,
    map_id, whiskerLeft_app, leftUnitor_hom_app, leftUnitor_inv_app, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit, Equivalence.symm_counit, Category.id_comp, cancelIso,
    Category.comp_id]
  have hc {Z Z' : C₄} (f : Z ⟶ Z') :
      L₂.map (R₂.map f) ≫ adj₂.counit.app Z' = adj₂.counit.app Z ≫ f :=
    adj₂.counit.naturality f
  have ha {Z Z' : C₂} (f : Z ⟶ Z') :
      G.map (R₁.map f) ≫ a.app Z' = a.app Z ≫ R₂.map (H.map f) :=
    a.naturality f
  slice_lhs 5 7 =>
    rw [← e₄.functor.map_comp_assoc, hc, e₄.functor.map_comp]
    simp only [id_obj, Category.assoc, Equivalence.functor_unit_comp, Category.comp_id]
  slice_lhs 3 4 =>
    rw [← e₄.functor.map_comp, ← L₂.map_comp, ha]
    simp only [Functor.comp_map, Functor.map_comp]
  slice_lhs 4 5 =>
    rw [← e₄.functor.map_comp, hc, e₄.functor.map_comp]

private def trSquare (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄)
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃} {I : C₃ ⥤ C₄}
    (q : F ⋙ G ≅ H ⋙ I) :
    trFunctor e₁ e₂ F ⋙ trFunctor e₂ e₄ G ≅
      trFunctor e₁ e₃ H ⋙ trFunctor e₃ e₄ I :=
  (trComp e₁ e₂ e₄ F G).symm ≪≫ trIso e₁ e₄ q ≪≫ trComp e₁ e₃ e₄ H I

variable {C₅ C₆ D₅ D₆ : Type*} [Category C₅] [Category C₆]
  [Category D₅] [Category D₆]

private theorem trSquare_comp (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄) (e₅ : C₅ ≌ D₅) (e₆ : C₆ ≌ D₆)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (FG : C₁ ⥤ C₃)
    (H : C₄ ⥤ C₅) (I : C₅ ⥤ C₆) (HI : C₄ ⥤ C₆)
    (R : C₁ ⥤ C₄) (S : C₂ ⥤ C₅) (T : C₃ ⥤ C₆)
    (q : F ⋙ S ≅ R ⋙ H) (r : G ⋙ T ≅ S ⋙ I) (t : FG ⋙ T ≅ R ⋙ HI)
    (c : FG ≅ F ⋙ G) (d : HI ≅ H ⋙ I)
    (hq : ∀ X, T.map (c.hom.app X) ≫ r.hom.app (F.obj X) ≫
      I.map (q.hom.app X) = t.hom.app X ≫ d.hom.app (R.obj X)) (X : D₁) :
    (trFunctor e₃ e₆ T).map
        ((trIso e₁ e₃ c ≪≫ trComp e₁ e₂ e₃ F G).hom.app X) ≫
      (trSquare e₂ e₃ e₅ e₆ r).hom.app ((trFunctor e₁ e₂ F).obj X) ≫
      (trFunctor e₅ e₆ I).map ((trSquare e₁ e₂ e₄ e₅ q).hom.app X) =
    (trSquare e₁ e₃ e₄ e₆ t).hom.app X ≫
      (trIso e₄ e₆ d ≪≫ trComp e₄ e₅ e₆ H I).hom.app
        ((trFunctor e₁ e₄ R).obj X) := by
  simp only [trFunctor, comp_obj, trIso, trComp, Equivalence.funInvIdAssoc, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, isoWhiskerLeft_trans, isoWhiskerRight_trans, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom, isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, id_obj, leftUnitor_inv_app, map_id,
    associator_hom_app, Category.comp_id, Category.id_comp, Functor.comp_map, map_comp,
    Equivalence.inv_fun_map, Category.assoc, Iso.hom_inv_id_app_assoc, trSquare,
    isoWhiskerLeft_inv, associator_inv_app, leftUnitor_hom_app, cancelIso]
  have hr (Z Z' : C₂) (f : Z ⟶ Z') :
      T.map (G.map f) ≫ r.hom.app Z' = r.hom.app Z ≫ I.map (S.map f) :=
    r.hom.naturality f
  have hd (Z Z' : C₄) (f : Z ⟶ Z') :
      HI.map f ≫ d.hom.app Z' = d.hom.app Z ≫ I.map (H.map f) :=
    d.hom.naturality f
  simp only [← e₆.functor.map_comp]
  congr 1
  rw [reassoc_of% hr, reassoc_of% hd]
  simp only [← I.map_comp_assoc]
  rw [← S.map_comp_assoc, Iso.hom_inv_id_app]
  erw [S.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hq]

private theorem trSquare_symm (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄)
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃} {I : C₃ ⥤ C₄}
    (q : F ⋙ G ≅ H ⋙ I) :
    trSquare e₁ e₃ e₂ e₄ q.symm = (trSquare e₁ e₂ e₃ e₄ q).symm := by
  simp only [trSquare, trIso_symm, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

private theorem rotate_square {C : Type*} [Category C] {V W X Y Z : C}
    (a : X ≅ Y) (b : Z ≅ Y) (c : W ≅ Z) (d : V ≅ X) (e : V ≅ W)
    (h : a.hom ≫ b.inv ≫ c.inv = d.inv ≫ e.hom) :
    e.hom ≫ c.hom ≫ b.hom = d.hom ≫ a.hom := by
  rw [← cancel_epi d.inv, ← cancel_mono b.inv, ← cancel_mono c.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

private theorem trSquare_paste (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄) (e₅ : C₅ ≌ D₅) (e₆ : C₆ ≌ D₆)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (FG : C₁ ⥤ C₃)
    (H : C₄ ⥤ C₅) (I : C₅ ⥤ C₆) (HI : C₄ ⥤ C₆)
    (R : C₁ ⥤ C₄) (S : C₂ ⥤ C₅) (T : C₃ ⥤ C₆)
    (q : R ⋙ H ≅ F ⋙ S) (r : S ⋙ I ≅ G ⋙ T) (t : R ⋙ HI ≅ FG ⋙ T)
    (c : FG ≅ F ⋙ G) (d : HI ≅ H ⋙ I)
    (hq : ∀ X, d.hom.app (R.obj X) ≫ I.map (q.hom.app X) ≫
      r.hom.app (F.obj X) = t.hom.app X ≫ T.map (c.hom.app X)) (X : D₁) :
    (trIso e₄ e₆ d ≪≫ trComp e₄ e₅ e₆ H I).hom.app
        ((trFunctor e₁ e₄ R).obj X) ≫
      (trFunctor e₅ e₆ I).map ((trSquare e₁ e₄ e₂ e₅ q).hom.app X) ≫
      (trSquare e₂ e₅ e₃ e₆ r).hom.app ((trFunctor e₁ e₂ F).obj X) =
    (trSquare e₁ e₄ e₃ e₆ t).hom.app X ≫
      (trFunctor e₃ e₆ T).map
        ((trIso e₁ e₃ c ≪≫ trComp e₁ e₂ e₃ F G).hom.app X) := by
  have hq' (Y : C₁) : T.map (c.hom.app Y) ≫ r.inv.app (F.obj Y) ≫
      I.map (q.inv.app Y) = t.inv.app Y ≫ d.hom.app (R.obj Y) := by
    exact rotate_square (d.app (R.obj Y)) (I.mapIso (q.app Y)).symm
      (r.app (F.obj Y)).symm (t.app Y).symm (T.mapIso (c.app Y)) (hq Y)
  have ht := trSquare_comp e₁ e₂ e₃ e₄ e₅ e₆ F G FG H I HI R S T
    q.symm r.symm t.symm c d hq' X
  simp only [trSquare_symm, Iso.symm_hom] at ht
  exact rotate_square
    ((trFunctor e₃ e₆ T).mapIso ((trIso e₁ e₃ c ≪≫ trComp e₁ e₂ e₃ F G).app X))
    ((trSquare e₂ e₅ e₃ e₆ r).app ((trFunctor e₁ e₂ F).obj X))
    ((trFunctor e₅ e₆ I).mapIso ((trSquare e₁ e₄ e₂ e₅ q).app X))
    ((trSquare e₁ e₄ e₃ e₆ t).app X)
    ((trIso e₄ e₆ d ≪≫ trComp e₄ e₅ e₆ H I).app ((trFunctor e₁ e₄ R).obj X)) ht

private theorem trSquare_paste_hom (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄) (e₅ : C₅ ≌ D₅) (e₆ : C₆ ≌ D₆)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (FG : C₁ ⥤ C₃)
    (H : C₄ ⥤ C₅) (I : C₅ ⥤ C₆) (HI : C₄ ⥤ C₆)
    (R : C₁ ⥤ C₄) (S : C₂ ⥤ C₅) (T : C₃ ⥤ C₆)
    (q : R ⋙ H ≅ F ⋙ S) (r : S ⋙ I ≅ G ⋙ T) (t : R ⋙ HI ≅ FG ⋙ T)
    (c : FG ≅ F ⋙ G) (d : HI ≅ H ⋙ I)
    (hq : ∀ X, d.hom.app (R.obj X) ≫ I.map (q.hom.app X) ≫
      r.hom.app (F.obj X) = t.hom.app X ≫ T.map (c.hom.app X)) :
    whiskerLeft (trFunctor e₁ e₄ R) (trIso e₄ e₆ d ≪≫ trComp e₄ e₅ e₆ H I).hom ≫
      whiskerRight (trSquare e₁ e₄ e₂ e₅ q).hom (trFunctor e₅ e₆ I) ≫
      whiskerLeft (trFunctor e₁ e₂ F) (trSquare e₂ e₅ e₃ e₆ r).hom =
    (trSquare e₁ e₄ e₃ e₆ t).hom ≫
      whiskerRight (trIso e₁ e₃ c ≪≫ trComp e₁ e₂ e₃ F G).hom (trFunctor e₃ e₆ T) := by
  apply NatTrans.ext
  funext X
  exact trSquare_paste e₁ e₂ e₃ e₄ e₅ e₆ F G FG H I HI R S T q r t c d hq X

private def trId (e : C₁ ≌ D₁) {F : C₁ ⥤ C₁} (a : F ≅ 𝟭 C₁) :
    trFunctor e e F ≅ 𝟭 D₁ := trIso e e a ≪≫ e.counitIso

private theorem trSquare_id (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₂) (L : C₁ ⥤ C₁)
    (q : F ⋙ G ≅ L ⋙ F) (eG : G ≅ 𝟭 C₂) (eL : L ≅ 𝟭 C₁)
    (hq : ∀ X, q.hom.app X ≫ F.map (eL.hom.app X) = eG.hom.app (F.obj X))
    (X : D₁) :
    (trSquare e f e f q).hom.app X ≫
      (trFunctor e f F).map ((trId e eL).hom.app X) =
      (trId f eG).hom.app ((trFunctor e f F).obj X) := by
  simp only [trFunctor, comp_obj, id_obj, trSquare, trComp, Equivalence.funInvIdAssoc,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, isoWhiskerLeft_trans,
    isoWhiskerRight_trans, trIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_inv,
    isoWhiskerRight_inv, Iso.symm_inv, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_inv_app, map_id, leftUnitor_hom_app,
    leftUnitor_inv_app, associator_hom_app, Category.comp_id, Category.id_comp, trId,
    Functor.comp_map, map_comp, Equivalence.inv_fun_map, Category.assoc,
    Equivalence.unit_inverse_comp, cancelIso]
  slice_lhs 2 3 => rw [← f.functor.map_comp, hq]
  rw [← f.functor.map_comp]
  have hn := eG.hom.naturality (f.unitInv.app (F.obj (e.inverse.obj X)))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [hn]
  rw [f.functor.map_comp]
  congr 1
  exact (f.counit_app_functor _).symm

private theorem mateHorizontal
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂) (I : C₂ ⥤ C₃) (J : D₂ ⥤ D₃)
    (K : C₁ ⥤ C₃) (T : D₁ ⥤ D₃)
    (a : R₁ ⋙ G ≅ H ⋙ R₂) (b : R₂ ⋙ I ≅ J ⋙ R₃) (c : R₁ ⋙ K ≅ T ⋙ R₃)
    (e : K ≅ G ⋙ I) (f : T ≅ H ⋙ J)
    (hc : ∀ X, e.hom.app (R₁.obj X) ≫ I.map (a.hom.app X) ≫
      b.hom.app (H.obj X) = c.hom.app X ≫ R₃.map (f.hom.app X)) :
    ((mateEquiv adj₁ adj₃).symm (TwoSquare.mk _ _ _ _ c.hom)) =
      whiskerRight e.hom L₃ ≫
      whiskerLeft G ((mateEquiv adj₂ adj₃).symm (TwoSquare.mk _ _ _ _ b.hom)) ≫
      whiskerRight ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ a.hom)) J ≫
      whiskerLeft L₁ f.inv := by
  have hs : (mateEquiv adj₁ adj₃).symm c.hom =
      ((((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ a.hom)).hComp
        ((mateEquiv adj₂ adj₃).symm (TwoSquare.mk _ _ _ _ b.hom))).whiskerTop e.hom).whiskerBottom
          f.inv := by
    apply (mateEquiv adj₁ adj₃).injective
    erw [Equiv.apply_symm_apply, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine NatTrans.ext (funext fun X ↦ ?_)
    simp only [TwoSquare.mk, TwoSquare.whiskerLeft_app,
      TwoSquare.whiskerRight_app]
    rw [← cancel_mono (R₃.map (f.hom.app X))]
    simp only [Category.assoc, ← R₃.map_comp, Iso.inv_hom_id_app]
    erw [R₃.map_id, Category.comp_id]
    simpa only [TwoSquare.vComp, TwoSquare.mk,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      associator_inv_app, Category.id_comp, Category.comp_id] using (hc X).symm
  apply NatTrans.ext
  funext X
  have ht := congr_app hs X
  try dsimp only [TwoSquare.mk] at ht
  simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc] using ht

private theorem mateVertical
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
    {L₁' : D₁ ⥤ D₂} {R₁' : D₂ ⥤ D₁} {L₂' : D₂ ⥤ D₃} {R₂' : D₃ ⥤ D₂}
    {L : C₁ ⥤ C₃} {R : C₃ ⥤ C₁} {L' : D₁ ⥤ D₃} {R' : D₃ ⥤ D₁}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (G : C₁ ⥤ D₁) (H : C₂ ⥤ D₂) (K : C₃ ⥤ D₃)
    (a : R₁ ⋙ G ≅ H ⋙ R₁') (b : R₂ ⋙ H ≅ K ⋙ R₂') (t : R ⋙ G ≅ K ⋙ R')
    (e : L ≅ L₁ ⋙ L₂) (e' : L' ≅ L₁' ⋙ L₂')
    (c : R ≅ R₂ ⋙ R₁) (c' : R' ≅ R₂' ⋙ R₁')
    (he : conjugateIsoEquiv (adj₁.comp adj₂) adj e = c.symm)
    (he' : conjugateIsoEquiv (adj₁'.comp adj₂') adj' e' = c'.symm)
    (hq : ∀ M, G.map (c.hom.app M) ≫ a.hom.app (R₂.obj M) ≫
      R₁'.map (b.hom.app M) = t.hom.app M ≫ c'.hom.app (K.obj M)) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ t.hom)) =
      whiskerLeft G e'.hom ≫
      whiskerRight ((mateEquiv adj₁ adj₁').symm (TwoSquare.mk _ _ _ _ a.hom)) L₂' ≫
      whiskerLeft L₁ ((mateEquiv adj₂ adj₂').symm (TwoSquare.mk _ _ _ _ b.hom)) ≫
      whiskerRight e.inv K := by
  have hs : (mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ t.hom) =
      ((((mateEquiv adj₁ adj₁').symm (TwoSquare.mk _ _ _ _ a.hom)).vComp
        ((mateEquiv adj₂ adj₂').symm (TwoSquare.mk _ _ _ _ b.hom))).whiskerRight
          e'.hom).whiskerLeft e.inv := by
    apply (mateEquiv adj
      adj').injective
    rw [Equiv.apply_symm_apply, conjugateEquiv_mateEquiv_vcomp _
      (adj₁.comp adj₂),
      mateEquiv_conjugateEquiv_vcomp _
        (adj₁'.comp adj₂'),
      mateEquiv_hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hc := congrArg Iso.inv he
    have hc' := congrArg Iso.hom he'
    change conjugateEquiv _ _ e.inv =
      c.hom at hc
    change conjugateEquiv _ _ e'.hom =
      c'.inv at hc'
    rw [hc, hc']
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [TwoSquare.mk, TwoSquare.whiskerTop_app,
      TwoSquare.whiskerBottom_app]
    rw [← cancel_mono (c'.hom.app
      (K.obj M))]
    simpa only [TwoSquare.hComp, TwoSquare.mk,
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
      associator_inv_app, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using
      (hq M).symm
  apply NatTrans.ext
  funext X
  have ht := congr_app hs X
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight,
    TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    TwoSquare.vComp, TwoSquare.mk, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using ht

private theorem mateHorizontalIdentity
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R)
    (G : C₁ ⥤ C₁) (H : C₂ ⥤ C₂) (a : R ⋙ G ≅ H ⋙ R)
    (e : G ≅ 𝟭 C₁) (f : H ≅ 𝟭 C₂)
    (hq : ∀ M, a.hom.app M ≫ R.map (f.hom.app M) = e.hom.app (R.obj M)) :
    ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ a.hom)) =
      whiskerRight e.hom L ≫ whiskerLeft L f.inv := by
  have hs : (mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ a.hom) =
      ((TwoSquare.hId (L)).whiskerTop
        e.hom).whiskerBottom
          f.inv := by
    apply (mateEquiv adj
      adj).injective
    rw [Equiv.apply_symm_apply, mateEquiv_whiskerTop_whiskerBottom, TwoSquare.hId,
      mateEquiv_unitors]
    refine NatTrans.ext (funext fun M ↦ ?_)
    dsimp only [TwoSquare.mk]
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      rightUnitor_hom_app, leftUnitor_inv_app,
      Category.comp_id]
    rw [← cancel_mono (R.map
      (f.hom.app M))]
    simp only [Category.assoc, ← R.map_comp,
      Iso.inv_hom_id_app]
    erw [R.map_id, Category.comp_id]
    erw [Category.comp_id]
    exact hq M
  apply NatTrans.ext
  funext K
  simpa only [Functor.id_obj, Functor.comp_obj, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.mk,
    TwoSquare.vId, TwoSquare.hId,
    TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app,
    rightUnitor_hom_app, leftUnitor_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] using congr_app hs K

private theorem mateVerticalIdentity
    {L R : C₁ ⥤ C₁} {L' R' : C₂ ⥤ C₂} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (G : C₁ ⥤ C₂) (a : R ⋙ G ≅ G ⋙ R')
    (e : L ≅ 𝟭 C₁) (e' : L' ≅ 𝟭 C₂) (c : R ≅ 𝟭 C₁) (c' : R' ≅ 𝟭 C₂)
    (he : conjugateIsoEquiv Adjunction.id adj e = c.symm)
    (he' : conjugateIsoEquiv Adjunction.id adj' e' = c'.symm)
    (hq : ∀ M, a.inv.app M ≫ G.map (c.hom.app M) = c'.hom.app (G.obj M)) :
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ a.hom)) =
      whiskerLeft G e'.hom ≫ whiskerRight e.inv G := by
  have hs : (mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ a.hom) =
      ((TwoSquare.vId G).whiskerRight
        e'.hom).whiskerLeft e.inv := by
    apply (mateEquiv adj
      adj').injective
    rw [Equiv.apply_symm_apply, conjugateEquiv_mateEquiv_vcomp _ Adjunction.id,
      mateEquiv_conjugateEquiv_vcomp _ Adjunction.id, TwoSquare.vId,
      mateEquiv_id_id_unitors]
    have hc := congrArg Iso.inv he
    have hc' := congrArg Iso.hom he'
    change conjugateEquiv _ _ e.inv =
      c.hom at hc
    change conjugateEquiv _ _ e'.hom =
      c'.inv at hc'
    rw [hc, hc']
    refine NatTrans.ext (funext fun M ↦ ?_)
    dsimp only [TwoSquare.mk]
    simp only [TwoSquare.whiskerTop_app]
    rw [← cancel_epi (a.inv.app M)]
    simp only [Iso.inv_hom_id_app]
    rw [reassoc_of% (hq M)]
    simp only [TwoSquare.whiskerBottom,
      NatTrans.comp_app, whiskerLeft_app, leftUnitor_hom_app,
      rightUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp, Iso.hom_inv_id_app]
    rfl
  apply NatTrans.ext
  funext K
  have ht := congr_app hs K
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.mk,
    TwoSquare.vId, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.id_obj, Functor.comp_obj] at ht
  erw [Category.id_comp] at ht
  simpa only [leftUnitor_inv_app, Category.comp_id, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc] using ht

private theorem inverseTwo {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : X ≅ Z) (c : Y ≅ Z)
    (h : a.hom = b.hom ≫ c.inv) : a.inv = c.hom ≫ b.inv := by
  have he : a = b ≪≫ c.symm := Iso.ext h
  exact congrArg Iso.inv he

private theorem inverseFour {C : Type*} [Category C] {X X₁ X₂ Y Z : C}
    (a : X ≅ Y) (b : X ≅ X₁) (c : X₁ ≅ X₂) (d : X₂ ≅ Z) (e : Y ≅ Z)
    (h : a.hom = b.hom ≫ c.hom ≫ d.hom ≫ e.inv) :
    a.inv = e.hom ≫ d.inv ≫ c.inv ≫ b.inv := by
  have he : a = b ≪≫ c ≪≫ d ≪≫ e.symm := Iso.ext h
  simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using congrArg Iso.inv he

end TransportCalculus

-- Check exact descent on the homotopy-category localization.
section ExactLocalizationCalculus

variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₁] [HasDerivedCategory D₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def dMap {F G : C₁ ⥤ D₁} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (whiskerRight (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)) DerivedCategory.Q)

private theorem dMap_iso {F G : C₁ ⥤ D₁} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ≅ G) :
    dMap a.hom = (mapDerivedCategoryNatIso a).hom := rfl

private theorem dMap_square
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ D₂) (G₁ : C₁ ⥤ D₁) (G₂ : D₁ ⥤ D₂)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategoryCompIso F₁ F₂).hom ≫ dMap q.hom ≫
      (mapDerivedCategoryCompIso G₁ G₂).inv = (mapDerivedCategorySquareIso q).hom := by
  rw [dMap_iso]
  rfl

private noncomputable def dUnit (L : C₁ ⥤ D₁) (R : D₁ ⥤ C₁)
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : 𝟭 C₁ ≅ L ⋙ R) : 𝟭 (DerivedCategory C₁) ≅ L.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  (mapDerivedCategoryIdIso C₁).symm ≪≫ mapDerivedCategoryNatIso η ≪≫
    (mapDerivedCategoryCompIso L R).symm

private theorem dUnit_fac (L : C₁ ⥤ D₁) (R : D₁ ⥤ C₁)
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : 𝟭 C₁ ≅ L ⋙ R) (X : HomotopyCategory C₁ (.up ℤ)) :
    (dUnit L R η).hom.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory η.hom (.up ℤ)).app X) := by
  simp only [dUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [mapDerivedCategoryCompIso_hom_app_factorsh L R X,
    mapDerivedCategoryNatIso_fach η X]
  rw [← mapDerivedCategoryIdIso_hom_app_Qh_obj C₁ X]
  exact Iso.inv_hom_id_app_assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem dSquare_fac
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ D₂) (G₁ : C₁ ⥤ D₁) (G₂ : D₁ ⥤ D₂)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (X : HomotopyCategory C₁ (.up ℤ)) :
    (mapDerivedCategorySquareIso q).hom.app (DerivedCategory.Qh.obj X) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory q.hom (.up ℤ)).app X) := by
  have hi : (mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Qh.obj X) ≫
      (F₁ ⋙ F₂).mapDerivedCategoryFactorsh.hom.app X =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso F₁ F₂).inv.app
      (DerivedCategory.Qh.obj X)), Iso.inv_hom_id_app_assoc]
    exact (mapDerivedCategoryCompIso_hom_app_factorsh F₁ F₂ X).symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [mapDerivedCategoryCompIso_hom_app_factorsh, mapDerivedCategoryNatIso_fach,
    ← Category.assoc, hi, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem dUnit_square
    (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂)
    (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (η₁ : 𝟭 C₁ ≅ L₁ ⋙ R₁) (η₂ : 𝟭 C₂ ≅ L₂ ⋙ R₂)
    (q : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hq : ∀ X, G.map (η₁.hom.app X) ≫ q.hom.app (L₁.obj X) =
      η₂.hom.app (G.obj X) ≫ R₂.map (b.hom.app X)) :
    whiskerRight (dUnit L₁ R₁ η₁).hom G.mapDerivedCategory ≫
      whiskerLeft L₁.mapDerivedCategory (mapDerivedCategorySquareIso q).hom =
    whiskerLeft G.mapDerivedCategory (dUnit L₂ R₂ η₂).hom ≫
      whiskerRight (mapDerivedCategorySquareIso b).hom R₂.mapDerivedCategory := by
  have hqh (X : HomotopyCategory C₁ (.up ℤ)) :
      (G.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory η₁.hom (.up ℤ)).app X) ≫
        (NatTrans.mapHomotopyCategory q.hom (.up ℤ)).app
          ((L₁.mapHomotopyCategory (.up ℤ)).obj X) =
      (NatTrans.mapHomotopyCategory η₂.hom (.up ℤ)).app
          ((G.mapHomotopyCategory (.up ℤ)).obj X) ≫
        (R₂.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app X) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    change (HomotopyCategory.quotient C₂ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₂ (.up ℤ)).map _ =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₂ (.up ℤ)).map _
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    exact hq (K.X n)
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (.up ℤ))
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [← cancel_mono
    (R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
        (L₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app
        ((L₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      R₂.mapDerivedCategoryFactorsh.hom.app
        ((H.mapHomotopyCategory (.up ℤ)).obj ((L₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  simp only [Category.assoc]
  have hnq := (mapDerivedCategorySquareIso q).hom.naturality
    (L₁.mapDerivedCategoryFactorsh.hom.app X)
  dsimp only [Functor.comp_map] at hnq
  erw [← reassoc_of% hnq, dSquare_fac _ _ _ _ q
    ((L₁.mapHomotopyCategory (.up ℤ)).obj X)]
  erw [← G.mapDerivedCategory.map_comp_assoc, ← G.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [dUnit_fac]
  erw [reassoc_of% G.mapDerivedCategoryFactorsh.hom.naturality]
  erw [← R₂.mapDerivedCategory.map_comp_assoc, ← R₂.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [dSquare_fac _ _ _ _ b X]
  simp only [Functor.map_comp, Category.assoc]
  have hnu := (dUnit L₂ R₂ η₂).hom.naturality
    (G.mapDerivedCategoryFactorsh.hom.app X)
  dsimp only [Functor.id_map, Functor.comp_map] at hnu
  erw [← reassoc_of% hnu, R₂.mapDerivedCategoryFactorsh.hom.naturality,
    reassoc_of% dUnit_fac L₂ R₂ η₂ ((G.mapHomotopyCategory (.up ℤ)).obj X)]
  have hh := congrArg
    (fun f ↦ G.mapDerivedCategoryFactorsh.hom.app X ≫ DerivedCategory.Qh.map f) (hqh X)
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [Functor.comp_map, Functor.map_comp] at hh ⊢
  exact hh

private theorem dUnit_square_inverse
    (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂)
    (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (η₁ : 𝟭 C₁ ≅ L₁ ⋙ R₁) (η₂ : 𝟭 C₂ ≅ L₂ ⋙ R₂)
    (q : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hq : ∀ X, G.map (η₁.hom.app X) ≫ q.hom.app (L₁.obj X) =
      η₂.hom.app (G.obj X) ≫ R₂.map (b.hom.app X)) (K : DerivedCategory C₁) :
    G.mapDerivedCategory.map ((dUnit L₁ R₁ η₁).hom.app K) ≫
      (mapDerivedCategorySquareIso q).hom.app (L₁.mapDerivedCategory.obj K) ≫
      R₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso b).inv.app K) =
    (dUnit L₂ R₂ η₂).hom.app (G.mapDerivedCategory.obj K) := by
  have h := NatTrans.congr_app (dUnit_square L₁ R₁ L₂ R₂ G H η₁ η₂ q b hq) K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at h
  rw [reassoc_of% h]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [R₂.mapDerivedCategory.map_id, Category.comp_id]

private theorem dMate_restriction
    (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂)
    (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂)
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [IsIso adj₁.unit] [IsIso adj₂.unit]
    (q : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hb : mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ b.hom) =
      TwoSquare.mk _ _ _ _ q.hom) (K : DerivedCategory C₁) :
    G.mapDerivedCategory.map (((mapDerivedCategoryIdIso C₁).inv ≫ dMap adj₁.unit ≫
      (mapDerivedCategoryCompIso L₁ R₁).inv).app K) ≫
      (mapDerivedCategorySquareIso q).hom.app (L₁.mapDerivedCategory.obj K) ≫
      R₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso b).inv.app K) =
    ((mapDerivedCategoryIdIso C₂).inv ≫ dMap adj₂.unit ≫
      (mapDerivedCategoryCompIso L₂ R₂).inv).app (G.mapDerivedCategory.obj K) := by
  rw [← asIso_hom adj₁.unit, ← asIso_hom adj₂.unit, dMap_iso, dMap_iso]
  apply dUnit_square_inverse L₁ R₁ L₂ R₂ G H (asIso adj₁.unit) (asIso adj₂.unit) q b
  intro X
  have h := unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ b.hom) X
  rw [hb] at h
  exact h

private theorem dSquare_symm
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ D₂) (G₁ : C₁ ⥤ D₁) (G₂ : D₁ ⥤ D₂)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    mapDerivedCategorySquareIso q.symm = (mapDerivedCategorySquareIso q).symm := by
  apply Iso.ext
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem dSquare_id_hom (R : C₁ ⥤ C₂) (P : C₁ ⥤ C₁) (p : C₂ ⥤ C₂)
    [R.Additive] [P.Additive] [p.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : R ⋙ p ≅ P ⋙ R) (eP : P ≅ 𝟭 C₁) (ep : p ≅ 𝟭 C₂)
    (hq : ∀ X, q.hom.app X ≫ R.map (eP.hom.app X) = ep.hom.app (R.obj X)) :
    (mapDerivedCategorySquareIso q).hom =
      whiskerLeft R.mapDerivedCategory
        (mapDerivedCategoryNatIso ep ≪≫ mapDerivedCategoryIdIso C₂).hom ≫
      whiskerRight (mapDerivedCategoryNatIso eP ≪≫
        mapDerivedCategoryIdIso C₁).inv R.mapDerivedCategory := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← cancel_mono (R.mapDerivedCategory.map
    ((mapDerivedCategoryNatIso eP ≪≫ mapDerivedCategoryIdIso C₁).hom.app K))]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [R.mapDerivedCategory.map_id, Category.comp_id]
  exact mapDerivedCategorySquareIso_hom_app_id q eP ep hq K

private theorem dSquare_id_inverse (R : C₁ ⥤ C₂) (P : C₁ ⥤ C₁) (p : C₂ ⥤ C₂)
    [R.Additive] [P.Additive] [p.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    (q : P ⋙ R ≅ R ⋙ p) (eP : P ≅ 𝟭 C₁) (ep : p ≅ 𝟭 C₂)
    (hq : q.hom = whiskerRight eP.hom R ≫ whiskerLeft R ep.inv) :
    (mapDerivedCategorySquareIso q).hom =
      whiskerRight (mapDerivedCategoryNatIso eP ≪≫ mapDerivedCategoryIdIso C₁).hom
        R.mapDerivedCategory ≫
      whiskerLeft R.mapDerivedCategory
        (mapDerivedCategoryNatIso ep ≪≫ mapDerivedCategoryIdIso C₂).inv := by
  have hi (X : C₁) : q.inv.app X ≫ R.map (eP.hom.app X) = ep.hom.app (R.obj X) := by
    rw [← cancel_epi (q.hom.app X), Iso.hom_inv_id_app_assoc, hq]
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have h := dSquare_id_hom R P p q.symm eP ep hi
  rw [dSquare_symm, Iso.symm_hom] at h
  rw [← cancel_epi (mapDerivedCategorySquareIso q).inv, Iso.inv_hom_id, h]
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc]
  rw [← Category.assoc
    (R.mapDerivedCategory.map ((mapDerivedCategoryNatIso eP ≪≫
      mapDerivedCategoryIdIso C₁).inv.app K))
    (R.mapDerivedCategory.map ((mapDerivedCategoryNatIso eP ≪≫
      mapDerivedCategoryIdIso C₁).hom.app K))]
  rw [← R.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

end ExactLocalizationCalculus


-- Apply the existing exact-square pasting theorems in both orientations.
section DerivedPasting

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem dSquare_comp_reverse
    (q₀₁ : U₀ ⋙ G₀₁ ≅ F₀₁ ⋙ U₁)
    (q₁₂ : U₁ ⋙ G₁₂ ≅ F₁₂ ⋙ U₂)
    (q₀₂ : U₀ ⋙ G₀₂ ≅ F₀₂ ⋙ U₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X, q₀₂.hom.app X ≫ U₂.map (cF.hom.app X) =
      cG.hom.app (U₀.obj X) ≫ G₁₂.map (q₀₁.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X)) :
    (mapDerivedCategorySquareIso q₀₂).hom =
      whiskerLeft U₀.mapDerivedCategory
        (mapDerivedCategoryNatIso cG ≪≫ (mapDerivedCategoryCompIso G₀₁ G₁₂).symm).hom ≫
      whiskerRight (mapDerivedCategorySquareIso q₀₁).hom G₁₂.mapDerivedCategory ≫
      whiskerLeft F₀₁.mapDerivedCategory (mapDerivedCategorySquareIso q₁₂).hom ≫
      whiskerRight (mapDerivedCategoryNatIso cF ≪≫
        (mapDerivedCategoryCompIso F₀₁ F₁₂).symm).inv U₂.mapDerivedCategory := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← cancel_mono (U₂.mapDerivedCategory.map
    ((mapDerivedCategoryNatIso cF ≪≫ (mapDerivedCategoryCompIso F₀₁ F₁₂).symm).hom.app K))]
  simp only [Category.assoc, ← U₂.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [U₂.mapDerivedCategory.map_id, Category.comp_id]
  exact mapDerivedCategorySquareIso_hom_app_comp q₀₁ q₁₂ q₀₂ cG cF hq K

private theorem dSquare_comp_forward
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X, U₂.map (cF.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X) ≫
      G₁₂.map (q₀₁.hom.app X) = q₀₂.hom.app X ≫ cG.hom.app (U₀.obj X)) :
    (mapDerivedCategorySquareIso q₀₂).hom =
      whiskerRight (mapDerivedCategoryNatIso cF ≪≫
        (mapDerivedCategoryCompIso F₀₁ F₁₂).symm).hom U₂.mapDerivedCategory ≫
      whiskerLeft F₀₁.mapDerivedCategory (mapDerivedCategorySquareIso q₁₂).hom ≫
      whiskerRight (mapDerivedCategorySquareIso q₀₁).hom G₁₂.mapDerivedCategory ≫
      whiskerLeft U₀.mapDerivedCategory
        (mapDerivedCategoryNatIso cG ≪≫ (mapDerivedCategoryCompIso G₀₁ G₁₂).symm).inv := by
  have h := mapDerivedCategorySquareIso_comp F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
    q₀₁ q₁₂ q₀₂ cF cG hq
  apply NatTrans.ext
  funext K
  have ht := congrArg (fun e ↦ e.hom.app K) h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Category.id_comp, Category.comp_id] at ht
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← cancel_mono ((mapDerivedCategoryNatIso cG ≪≫
    (mapDerivedCategoryCompIso G₀₁ G₁₂).symm).hom.app (U₀.mapDerivedCategory.obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact ht.symm

end DerivedPasting
private theorem sfPullback_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    eqToIso (congrArg (sfIntrinsicPullback A) h) =
      sfIntrinsicTransportIso A
        (ProEtale.upperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h) := by
  subst h
  exact (trIso_refl (sfIntrinsicModuleEquivalence Y A)
    (sfIntrinsicModuleEquivalence X A)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)).symm

private theorem sfSquare_transport {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicSquarePullback A gU j' j g w =
      (sfIntrinsicTransportComp A
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU)).symm ≪≫
      sfIntrinsicTransportIso A
        (ProEtale.upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w) ≪≫
      sfIntrinsicTransportComp A
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j') := by
  rw [sfIntrinsicSquarePullback, sfPullback_congr A w]
  exact trIso_path (sfIntrinsicModuleEquivalence Y A)
    (sfIntrinsicModuleEquivalence U' A) _ _ _ _ _

private theorem sfSquare_horizontal {U'' U' U Y'' Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (hU : U'' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (j'' : U'' ⟶ Y'') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (w : gU ≫ j = j' ≫ g) (w' : hU ≫ j' = j'' ≫ h)
    (w'' : (hU ≫ gU) ≫ j = j'' ≫ (h ≫ g))
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (sfIntrinsicPullbackComp A hU gU).hom.app ((sfIntrinsicPullback A j).obj M) ≫
      (sfIntrinsicPullback A hU).map
        ((sfIntrinsicSquarePullback A gU j' j g w).hom.app M) ≫
      (sfIntrinsicSquarePullback A hU j'' j' h w').hom.app
        ((sfIntrinsicPullback A g).obj M) =
    (sfIntrinsicSquarePullback A (hU ≫ gU) j'' j (h ≫ g) w'').hom.app M ≫
      (sfIntrinsicPullback A j'').map ((sfIntrinsicPullbackComp A h g).hom.app M) := by
  have hs :
      whiskerLeft (sfIntrinsicPullback A j) (sfIntrinsicPullbackComp A hU gU).hom ≫
        whiskerRight (sfIntrinsicSquarePullback A gU j' j g w).hom
          (sfIntrinsicPullback A hU) ≫
        whiskerLeft (sfIntrinsicPullback A g)
          (sfIntrinsicSquarePullback A hU j'' j' h w').hom =
      (sfIntrinsicSquarePullback A (hU ≫ gU) j'' j (h ≫ g) w'').hom ≫
        whiskerRight (sfIntrinsicPullbackComp A h g).hom (sfIntrinsicPullback A j'') := by
    rw [sfSquare_transport A gU j' j g w,
      sfSquare_transport A hU j'' j' h w',
      sfSquare_transport A (hU ≫ gU) j'' j (h ≫ g) w'']
    exact trSquare_paste_hom (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence Y' A) (sfIntrinsicModuleEquivalence Y'' A)
      (sfIntrinsicModuleEquivalence U A) (sfIntrinsicModuleEquivalence U' A)
      (sfIntrinsicModuleEquivalence U'' A)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (h ≫ g))
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hU)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (hU ≫ gU))
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j')
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j'')
      (ProEtale.upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w)
      (ProEtale.upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w')
      (ProEtale.upperStarCompIso (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w'')
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h g)
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hU gU)
      (ProEtale.upperStarCompIso_hom_app_paste
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) w w' w'')
  exact NatTrans.congr_app hs M

private theorem sfSquare_symm {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicSquarePullback A j' gU g j w.symm =
      (sfIntrinsicSquarePullback A gU j' j g w).symm := by
  simp only [sfIntrinsicSquarePullback, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]
  apply congrArg (fun e ↦ (sfIntrinsicPullbackComp A j' g).symm ≪≫ e ≪≫
    sfIntrinsicPullbackComp A gU j)
  apply Iso.ext
  simp only [eqToIso.hom, Iso.symm_hom, eqToIso.inv]

private theorem sfSquare_vertical {V' V U' U Y' Y : Scheme.{u}}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (gV : V' ⟶ V) (gU : U' ⟶ U) (g : Y' ⟶ Y)
    (w : gU ≫ j = j' ≫ g) (w' : gV ≫ i = i' ≫ gU)
    (w'' : gV ≫ (i ≫ j) = (i' ≫ j') ≫ g)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (sfIntrinsicPullback A gV).map ((sfIntrinsicPullbackComp A i j).hom.app M) ≫
      (sfIntrinsicSquarePullback A gV i' i gU w').hom.app
        ((sfIntrinsicPullback A j).obj M) ≫
      (sfIntrinsicPullback A i').map
        ((sfIntrinsicSquarePullback A gU j' j g w).hom.app M) =
    (sfIntrinsicSquarePullback A gV (i' ≫ j') (i ≫ j) g w'').hom.app M ≫
      (sfIntrinsicPullbackComp A i' j').hom.app ((sfIntrinsicPullback A g).obj M) := by
  have h := sfSquare_horizontal A j' i' g gU gV j i w.symm w'.symm w''.symm M
  rw [sfSquare_symm A gU j' j g w, sfSquare_symm A gV i' i gU w',
    sfSquare_symm A gV (i' ≫ j') (i ≫ j) g w''] at h
  exact rotate_square
    ((sfIntrinsicPullbackComp A i' j').app ((sfIntrinsicPullback A g).obj M))
    ((sfIntrinsicPullback A i').mapIso
      ((sfIntrinsicSquarePullback A gU j' j g w).app M))
    ((sfIntrinsicSquarePullback A gV i' i gU w').app
      ((sfIntrinsicPullback A j).obj M))
    ((sfIntrinsicSquarePullback A gV (i' ≫ j') (i ≫ j) g w'').app M)
    ((sfIntrinsicPullback A gV).mapIso ((sfIntrinsicPullbackComp A i j).app M)) h

private theorem sfSquare_identity {U Y : Scheme.{u}} (j : U ⟶ Y)
    (w : 𝟙 U ≫ j = j ≫ 𝟙 Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (sfIntrinsicSquarePullback A (𝟙 U) j j (𝟙 Y) w).hom.app M ≫
      (sfIntrinsicPullback A j).map ((sfIntrinsicPullbackId A Y).hom.app M) =
      (sfIntrinsicPullbackId A U).hom.app ((sfIntrinsicPullback A j).obj M) := by
  rw [sfSquare_transport]
  apply trSquare_id
  intro N
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  rw [ProEtale.upperStarCompIso_eq_upperStarFactor B w (Category.id_comp j)
    (Category.comp_id j)]
  simp only [ProEtale.upperStarFactor, ProEtale.upperStarComp_id_left,
    ProEtale.upperStarComp_id_right, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_inv, whiskerLeft_app, whiskerRight_app,
    Iso.symm_inv, Category.assoc]
  simp
  rfl

private theorem sfOpenMate_transport {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicOpenMate A gU j' j g w =
      (sfIntrinsicTransportComp A
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU)
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j')).inv ≫
      trNat (sfIntrinsicModuleEquivalence U A) (sfIntrinsicModuleEquivalence Y' A)
        (ProEtale.openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⟨w⟩) ≫
      (sfIntrinsicTransportComp A
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)).hom := by
  let M := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hm : ((mateEquiv (ProEtale.openImmersionLowerShriekUpperStarAdjunction M j)
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction M j')).symm
      (ProEtale.upperStarCompIso M w).hom) =
      ProEtale.openImmersionLowerShriekBaseChangeMap M ⟨w⟩ := by
    exact
      ((mateEquiv _ _).symm_apply_apply
        (ProEtale.openImmersionLowerShriekBaseChangeMap M ⟨w⟩) |>.symm.trans
        (congrArg (mateEquiv _ _).symm
          (ProEtale.mateEquiv_openImmersionLowerShriekBaseChangeMap M ⟨w⟩))).symm
  have h := trMate (sfIntrinsicModuleEquivalence U A)
    (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence U' A)
    (sfIntrinsicModuleEquivalence Y' A)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction M j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction M j')
    (ProEtale.upperStar M gU) (ProEtale.upperStar M g)
    (ProEtale.upperStarCompIso M w).hom
  rw [hm] at h
  unfold sfIntrinsicOpenMate
  rw [← rawMate_eq, sfSquare_transport]
  exact h

private theorem sfOpenMate_eq_mate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    sfIntrinsicOpenMate A gU j' j g w =
      ((mateEquiv (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')).symm
        (TwoSquare.mk _ _ _ _
          (sfIntrinsicSquarePullback A gU j' j g w).hom)) := by
  exact (rawMate_eq (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
    (sfIntrinsicPullback A gU) (sfIntrinsicPullback A g)
    (sfIntrinsicSquarePullback A gU j' j g w).hom).symm

attribute [local irreducible] sfIntrinsicOpenMate sfIntrinsicOpenAdjunction
  sfIntrinsicPullback sfIntrinsicExtensionByZero sfIntrinsicSquarePullback
  sfIntrinsicPullbackComp sfIntrinsicPullbackId sfIntrinsicOpenComp sfIntrinsicOpenId

private theorem sfOpenMate_mate {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g) :
    mateEquiv (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
      (sfIntrinsicOpenMate A gU j' j g w) =
      (sfIntrinsicSquarePullback A gU j' j g w).hom := by
  rw [sfOpenMate_eq_mate]
  exact (mateEquiv _ _).apply_symm_apply _

private theorem sfMate_horizontal {U'' U' U Y'' Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (hU : U'' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (j'' : U'' ⟶ Y'') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (w : gU ≫ j = j' ≫ g) (w' : hU ≫ j' = j'' ≫ h)
    (w'' : (hU ≫ gU) ≫ j = j'' ≫ (h ≫ g)) :
    sfIntrinsicOpenMate A (hU ≫ gU) j'' j (h ≫ g) w'' =
      whiskerRight (sfIntrinsicPullbackComp A hU gU).hom
        (sfIntrinsicExtensionByZero j'' A) ≫
      whiskerLeft (sfIntrinsicPullback A gU) (sfIntrinsicOpenMate A hU j'' j' h w') ≫
      whiskerRight (sfIntrinsicOpenMate A gU j' j g w) (sfIntrinsicPullback A h) ≫
      whiskerLeft (sfIntrinsicExtensionByZero j A) (sfIntrinsicPullbackComp A h g).inv := by
  simpa only [← sfOpenMate_eq_mate] using
    mateHorizontal (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
    (sfIntrinsicOpenAdjunction A j'')
    (sfIntrinsicPullback A gU) (sfIntrinsicPullback A g)
    (sfIntrinsicPullback A hU) (sfIntrinsicPullback A h)
    (sfIntrinsicPullback A (hU ≫ gU)) (sfIntrinsicPullback A (h ≫ g))
    (sfIntrinsicSquarePullback A gU j' j g w)
    (sfIntrinsicSquarePullback A hU j'' j' h w')
    (sfIntrinsicSquarePullback A (hU ≫ gU) j'' j (h ≫ g) w'')
    (sfIntrinsicPullbackComp A hU gU) (sfIntrinsicPullbackComp A h g)
    (sfSquare_horizontal A gU hU j j' j'' g h w w' w'')

private theorem sfOpenComp_conjugate {V U Y : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j] :
    conjugateIsoEquiv ((sfIntrinsicOpenAdjunction A i).comp (sfIntrinsicOpenAdjunction A j))
      (sfIntrinsicOpenAdjunction A (i ≫ j)) (sfIntrinsicOpenComp A i j) =
      (sfIntrinsicPullbackComp A i j).symm := by
  unfold sfIntrinsicOpenComp
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro M
  exact (Adjunction.unit_leftAdjointUniq_hom_app
    (sfIntrinsicOpenAdjunction A (i ≫ j))
    (((sfIntrinsicOpenAdjunction A i).comp (sfIntrinsicOpenAdjunction A j)).ofNatIsoRight
      (sfIntrinsicPullbackComp A i j).symm) M).symm

private theorem sfMate_vertical {V' V U' U Y' Y : Scheme.{u}}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (gV : V' ⟶ V) (gU : U' ⟶ U) (g : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion i'] [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) (w' : gV ≫ i = i' ≫ gU)
    (w'' : gV ≫ (i ≫ j) = (i' ≫ j') ≫ g) :
    sfIntrinsicOpenMate A gV (i' ≫ j') (i ≫ j) g w'' =
      whiskerLeft (sfIntrinsicPullback A gV) (sfIntrinsicOpenComp A i' j').hom ≫
      whiskerRight (sfIntrinsicOpenMate A gV i' i gU w')
        (sfIntrinsicExtensionByZero j' A) ≫
      whiskerLeft (sfIntrinsicExtensionByZero i A) (sfIntrinsicOpenMate A gU j' j g w) ≫
      whiskerRight (sfIntrinsicOpenComp A i j).inv (sfIntrinsicPullback A g) := by
  simpa only [← sfOpenMate_eq_mate] using
    mateVertical (sfIntrinsicOpenAdjunction A i) (sfIntrinsicOpenAdjunction A j)
      (sfIntrinsicOpenAdjunction A i') (sfIntrinsicOpenAdjunction A j')
      (sfIntrinsicOpenAdjunction A (i ≫ j)) (sfIntrinsicOpenAdjunction A (i' ≫ j'))
      (sfIntrinsicPullback A gV) (sfIntrinsicPullback A gU) (sfIntrinsicPullback A g)
      (sfIntrinsicSquarePullback A gV i' i gU w')
      (sfIntrinsicSquarePullback A gU j' j g w)
      (sfIntrinsicSquarePullback A gV (i' ≫ j') (i ≫ j) g w'')
      (sfIntrinsicOpenComp A i j) (sfIntrinsicOpenComp A i' j')
      (sfIntrinsicPullbackComp A i j) (sfIntrinsicPullbackComp A i' j')
      (sfOpenComp_conjugate A i j) (sfOpenComp_conjugate A i' j')
      (sfSquare_vertical A i i' j j' gV gU g w w' w'')

private theorem sfMate_horizontal_id {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (w : 𝟙 U ≫ j = j ≫ 𝟙 Y) :
    sfIntrinsicOpenMate A (𝟙 U) j j (𝟙 Y) w =
      whiskerRight (sfIntrinsicPullbackId A U).hom (sfIntrinsicExtensionByZero j A) ≫
      whiskerLeft (sfIntrinsicExtensionByZero j A) (sfIntrinsicPullbackId A Y).inv := by
  simpa only [← sfOpenMate_eq_mate] using
    mateHorizontalIdentity (sfIntrinsicOpenAdjunction A j)
      (sfIntrinsicPullback A (𝟙 U)) (sfIntrinsicPullback A (𝟙 Y))
      (sfIntrinsicSquarePullback A (𝟙 U) j j (𝟙 Y) w)
      (sfIntrinsicPullbackId A U) (sfIntrinsicPullbackId A Y) (sfSquare_identity A j w)

attribute [local semireducible] sfIntrinsicOpenId

private theorem sfOpenId_conjugate (Y : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (sfIntrinsicOpenAdjunction A (𝟙 Y))
      (sfIntrinsicOpenId A Y) = (sfIntrinsicPullbackId A Y).symm := by
  unfold sfIntrinsicOpenId
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro M
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((sfIntrinsicOpenAdjunction A (𝟙 Y)).ofNatIsoRight (sfIntrinsicPullbackId A Y))
    Adjunction.id M
  change (sfIntrinsicOpenAdjunction A (𝟙 Y)).unit.app M ≫
    (sfIntrinsicPullbackId A Y).hom.app ((sfIntrinsicExtensionByZero (𝟙 Y) A).obj M) ≫
    (sfIntrinsicOpenId A Y).hom.app M = 𝟙 M at hu
  change (sfIntrinsicPullbackId A Y).inv.app M =
    (sfIntrinsicOpenAdjunction A (𝟙 Y)).unit.app M ≫
      (sfIntrinsicPullback A (𝟙 Y)).map ((sfIntrinsicOpenId A Y).hom.app M)
  rw [← cancel_mono ((sfIntrinsicPullbackId A Y).hom.app M), Iso.inv_hom_id_app,
    Category.assoc]
  erw [(sfIntrinsicPullbackId A Y).hom.naturality]
  exact hu.symm

attribute [local irreducible] sfIntrinsicOpenId

private theorem sfMate_vertical_id {X Y : Scheme.{u}} (g : X ⟶ Y)
    (w : g ≫ 𝟙 Y = 𝟙 X ≫ g) :
    sfIntrinsicOpenMate A g (𝟙 X) (𝟙 Y) g w =
      whiskerLeft (sfIntrinsicPullback A g) (sfIntrinsicOpenId A X).hom ≫
      whiskerRight (sfIntrinsicOpenId A Y).inv (sfIntrinsicPullback A g) := by
  have hq (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
      (sfIntrinsicSquarePullback A g (𝟙 X) (𝟙 Y) g w).inv.app M ≫
        (sfIntrinsicPullback A g).map ((sfIntrinsicPullbackId A Y).hom.app M) =
      (sfIntrinsicPullbackId A X).hom.app ((sfIntrinsicPullback A g).obj M) := by
    have he := congrArg (fun e ↦ e.inv.app M)
      (sfSquare_symm A (𝟙 X) g g (𝟙 Y) w.symm)
    rw [he]
    exact sfSquare_identity A g w.symm M
  simpa only [← sfOpenMate_eq_mate] using
    mateVerticalIdentity (sfIntrinsicOpenAdjunction A (𝟙 Y))
      (sfIntrinsicOpenAdjunction A (𝟙 X)) (sfIntrinsicPullback A g)
      (sfIntrinsicSquarePullback A g (𝟙 X) (𝟙 Y) g w)
      (sfIntrinsicOpenId A Y) (sfIntrinsicOpenId A X)
      (sfIntrinsicPullbackId A Y) (sfIntrinsicPullbackId A X)
      (sfOpenId_conjugate A Y) (sfOpenId_conjugate A X) hq

private theorem sfOpenMate_isIso {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    IsIso (sfIntrinsicOpenMate A gU j' j g sq.w) := by
  rw [sfOpenMate_transport]
  unfold sfIntrinsicPullback sfIntrinsicExtensionByZero
  have hraw : IsIso (ProEtale.openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⟨sq.w⟩) :=
    ProEtale.isIso_openImmersionLowerShriekBaseChangeMap _ sq
  let b := isoWhiskerLeft (sfIntrinsicModuleEquivalence U A).inverse
    (isoWhiskerRight (asIso (ProEtale.openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⟨sq.w⟩))
      (sfIntrinsicModuleEquivalence Y' A).functor)
  change IsIso (((sfIntrinsicTransportComp A
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) gU)
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j')).symm ≪≫
    b ≪≫ sfIntrinsicTransportComp A
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)).hom)
  infer_instance

private noncomputable def sfMateIso {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j' ≅
      sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g :=
  letI := sfOpenMate_isIso A gU j' j g sq
  mapDerivedCategorySquareIso (asIso (sfIntrinsicOpenMate A gU j' j g sq.w))

private noncomputable def sfExchange {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
      sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j' :=
  (sfMateIso A gU j' j g sq).symm

private theorem sfExchange_hom {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    (sfExchange A gU j' j g sq).hom = (sfMateIso A gU j' j g sq).inv := rfl

private theorem sfOpenUnit_isIso {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] : IsIso (sfIntrinsicOpenAdjunction A j).unit := by
  have : (sfIntrinsicExtensionByZero j A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  exact (sfIntrinsicOpenAdjunction A j).unit_isIso_of_L_fully_faithful

private theorem sfDerivedMate_eq {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : gU ≫ j = j' ≫ g)
    [IsIso (sfIntrinsicOpenMate A gU j' j g w)] :
    sfIntrinsicDerivedOpenMate A gU j' j g w =
      (mapDerivedCategorySquareIso (asIso (sfIntrinsicOpenMate A gU j' j g w))).hom := by
  rfl

private theorem sfExchange_canonical {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g) :
    (sfExchange A gU j' j g sq).inv = sfIntrinsicDerivedOpenMate A gU j' j g sq.w := by
  have := sfOpenMate_isIso A gU j' j g sq
  exact (sfDerivedMate_eq A gU j' j g sq.w).symm

attribute [local irreducible] sfMateIso sfExchange sfIntrinsicDerivedOpenMate
  sfIntrinsicDerivedOpenUnit sfIntrinsicDerivedSquarePullback
  sfIntrinsicDerivedPullbackComp sfIntrinsicDerivedOpenComp
  sfIntrinsicDerivedPullbackId sfIntrinsicDerivedOpenId

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
private theorem sfRestriction {U' U Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ Y') (j : U ⟶ Y) (g : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback gU j' j g)
    (K : proEtaleDerivedCategory U A) :
    (sfIntrinsicDerivedPullback A gU).map ((sfIntrinsicDerivedOpenUnit A j).app K) ≫
      (sfIntrinsicDerivedSquarePullback A gU j' j g sq.w).hom.app
        ((sfIntrinsicDerivedOpen A j).obj K) ≫
      (sfIntrinsicDerivedPullback A j').map ((sfExchange A gU j' j g sq).hom.app K) =
        (sfIntrinsicDerivedOpenUnit A j').app ((sfIntrinsicDerivedPullback A gU).obj K) := by
  have hmate {C₁ C₂ D₁ D₂ : Type (u + 2)}
      [Category.{u + 1} C₁] [Category.{u + 1} C₂]
      [Category.{u + 1} D₁] [Category.{u + 1} D₂]
      [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
      [HasDerivedCategory.{u + 2} C₁] [HasDerivedCategory.{u + 2} C₂]
      [HasDerivedCategory.{u + 2} D₁] [HasDerivedCategory.{u + 2} D₂]
      (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂)
      (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂)
      [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
      [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
      [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
      [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
      [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
      [PreservesFiniteLimits G] [PreservesFiniteColimits G]
      [PreservesFiniteLimits H] [PreservesFiniteColimits H]
      (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
      [IsIso adj₁.unit] [IsIso adj₂.unit]
      (q : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
      (hb : mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ b.hom) =
        TwoSquare.mk _ _ _ _ q.hom) (K : DerivedCategory C₁) :
      G.mapDerivedCategory.map (((mapDerivedCategoryIdIso C₁).inv ≫ dMap adj₁.unit ≫
        (mapDerivedCategoryCompIso L₁ R₁).inv).app K) ≫
        (mapDerivedCategorySquareIso q).hom.app (L₁.mapDerivedCategory.obj K) ≫
        R₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso b).inv.app K) =
      ((mapDerivedCategoryIdIso C₂).inv ≫ dMap adj₂.unit ≫
        (mapDerivedCategoryCompIso L₂ R₂).inv).app (G.mapDerivedCategory.obj K) := by
    rw [← asIso_hom adj₁.unit, ← asIso_hom adj₂.unit, dMap_iso, dMap_iso]
    apply dUnit_square_inverse L₁ R₁ L₂ R₂ G H (asIso adj₁.unit) (asIso adj₂.unit) q b
    intro X
    have h := unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ b.hom) X
    rw [hb] at h
    exact h
  have := sfOpenUnit_isIso A j
  have := sfOpenUnit_isIso A j'
  have := sfOpenMate_isIso A gU j' j g sq
  unfold sfIntrinsicDerivedOpenUnit sfIntrinsicDerivedSquarePullback sfExchange sfMateIso
  exact hmate (sfIntrinsicExtensionByZero j A) (sfIntrinsicPullback A j)
    (sfIntrinsicExtensionByZero j' A) (sfIntrinsicPullback A j')
    (sfIntrinsicPullback A gU) (sfIntrinsicPullback A g)
    (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
    (sfIntrinsicSquarePullback A gU j' j g sq.w)
    (asIso (sfIntrinsicOpenMate A gU j' j g sq.w)) (sfOpenMate_mate A gU j' j g sq.w) K

private theorem sfDerivedMate_horizontal {U'' U' U Y'' Y' Y : Scheme.{u}}
    (gU : U' ⟶ U) (hU : U'' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (j'' : U'' ⟶ Y'') (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (sq : IsPullback gU j' j g) (sq' : IsPullback hU j'' j' h)
    (outer : IsPullback (hU ≫ gU) j'' j (h ≫ g)) :
    (sfMateIso A (hU ≫ gU) j'' j (h ≫ g) outer).hom =
      whiskerRight (sfIntrinsicDerivedPullbackComp A hU gU).hom
        (sfIntrinsicDerivedOpen A j'') ≫
      whiskerLeft (sfIntrinsicDerivedPullback A gU)
        ((sfMateIso A hU j'' j' h sq').hom) ≫
      whiskerRight ((sfMateIso A gU j' j g sq).hom)
        (sfIntrinsicDerivedPullback A h) ≫
      whiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackComp A h g).inv := by
  have := sfOpenMate_isIso A gU j' j g sq
  have := sfOpenMate_isIso A hU j'' j' h sq'
  have := sfOpenMate_isIso A (hU ≫ gU) j'' j (h ≫ g) outer
  have hq (M : proEtaleRingModules U (proEtaleConstantRing U A)) :
      (sfIntrinsicExtensionByZero j'' A).map
          ((sfIntrinsicPullbackComp A hU gU).hom.app M) ≫
        (sfIntrinsicOpenMate A hU j'' j' h sq'.w).app ((sfIntrinsicPullback A gU).obj M) ≫
        (sfIntrinsicPullback A h).map ((sfIntrinsicOpenMate A gU j' j g sq.w).app M) =
      (sfIntrinsicOpenMate A (hU ≫ gU) j'' j (h ≫ g) outer.w).app M ≫
        (sfIntrinsicPullbackComp A h g).hom.app ((sfIntrinsicExtensionByZero j A).obj M) := by
    rw [sfMate_horizontal A gU hU j j' j'' g h sq.w sq'.w outer.w]
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hcomp := mapDerivedCategorySquareIso_comp
    (sfIntrinsicPullback A gU) (sfIntrinsicPullback A hU)
    (sfIntrinsicPullback A (hU ≫ gU)) (sfIntrinsicPullback A g) (sfIntrinsicPullback A h)
    (sfIntrinsicPullback A (h ≫ g)) (sfIntrinsicExtensionByZero j A)
    (sfIntrinsicExtensionByZero j' A) (sfIntrinsicExtensionByZero j'' A)
    (asIso (sfIntrinsicOpenMate A gU j' j g sq.w))
    (asIso (sfIntrinsicOpenMate A hU j'' j' h sq'.w))
    (asIso (sfIntrinsicOpenMate A (hU ≫ gU) j'' j (h ≫ g) outer.w))
    (sfIntrinsicPullbackComp A hU gU) (sfIntrinsicPullbackComp A h g) hq
  apply NatTrans.ext
  funext K
  have ht := congrArg (fun e ↦ e.hom.app K) hcomp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Category.id_comp, Category.comp_id] at ht
  simp only [sfMateIso, sfIntrinsicDerivedPullbackComp, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app]
  rw [← cancel_mono ((mapDerivedCategoryNatIso (sfIntrinsicPullbackComp A h g) ≪≫
    (mapDerivedCategoryCompIso (sfIntrinsicPullback A g) (sfIntrinsicPullback A h)).symm).hom.app
      ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact ht.symm

private theorem sfDerivedMate_vertical {V' V U' U Y' Y : Scheme.{u}}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ Y) (j' : U' ⟶ Y')
    (gV : V' ⟶ V) (gU : U' ⟶ U) (g : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion i'] [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) (sq' : IsPullback gV i' i gU)
    (outer : IsPullback gV (i' ≫ j') (i ≫ j) g) :
    (sfMateIso A gV (i' ≫ j') (i ≫ j) g outer).hom =
      whiskerLeft (sfIntrinsicDerivedPullback A gV) (sfIntrinsicDerivedOpenComp A i' j').hom ≫
      whiskerRight ((sfMateIso A gV i' i gU sq').hom)
        (sfIntrinsicDerivedOpen A j') ≫
      whiskerLeft (sfIntrinsicDerivedOpen A i) ((sfMateIso A gU j' j g sq).hom) ≫
      whiskerRight (sfIntrinsicDerivedOpenComp A i j).inv (sfIntrinsicDerivedPullback A g) := by
  have := sfOpenMate_isIso A gV i' i gU sq'
  have := sfOpenMate_isIso A gU j' j g sq
  have := sfOpenMate_isIso A gV (i' ≫ j') (i ≫ j) g outer
  have hq (M : proEtaleRingModules V (proEtaleConstantRing V A)) :
      (sfIntrinsicOpenMate A gV (i' ≫ j') (i ≫ j) g outer.w).app M ≫
        (sfIntrinsicPullback A g).map ((sfIntrinsicOpenComp A i j).hom.app M) =
      (sfIntrinsicOpenComp A i' j').hom.app ((sfIntrinsicPullback A gV).obj M) ≫
        (sfIntrinsicExtensionByZero j' A).map ((sfIntrinsicOpenMate A gV i' i gU sq'.w).app M) ≫
        (sfIntrinsicOpenMate A gU j' j g sq.w).app ((sfIntrinsicExtensionByZero i A).obj M) := by
    rw [sfMate_vertical A i i' j j' gV gU g sq.w sq'.w outer.w]
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc,
      ← (sfIntrinsicPullback A g).map_comp, Iso.inv_hom_id_app]
    erw [(sfIntrinsicPullback A g).map_id, Category.comp_id]
  apply NatTrans.ext
  funext K
  simp only [sfMateIso, sfIntrinsicDerivedOpenComp, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app]
  rw [← cancel_mono ((sfIntrinsicPullback A g).mapDerivedCategory.map
    ((mapDerivedCategoryNatIso (sfIntrinsicOpenComp A i j) ≪≫
      (mapDerivedCategoryCompIso (sfIntrinsicExtensionByZero i A)
        (sfIntrinsicExtensionByZero j A)).symm).hom.app K))]
  simp only [Category.assoc, ← (sfIntrinsicPullback A g).mapDerivedCategory.map_comp,
    Iso.inv_hom_id_app]
  erw [(sfIntrinsicPullback A g).mapDerivedCategory.map_id, Category.comp_id]
  exact mapDerivedCategorySquareIso_hom_app_comp
    (asIso (sfIntrinsicOpenMate A gV i' i gU sq'.w))
    (asIso (sfIntrinsicOpenMate A gU j' j g sq.w))
    (asIso (sfIntrinsicOpenMate A gV (i' ≫ j') (i ≫ j) g outer.w))
    (sfIntrinsicOpenComp A i' j') (sfIntrinsicOpenComp A i j) hq K

private theorem sfDerivedMate_horizontal_id {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (sq : IsPullback (𝟙 U) j j (𝟙 Y)) :
    (sfMateIso A (𝟙 U) j j (𝟙 Y) sq).hom =
      whiskerRight (sfIntrinsicDerivedPullbackId A U).hom (sfIntrinsicDerivedOpen A j) ≫
      whiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackId A Y).inv := by
  have := sfOpenMate_isIso A (𝟙 U) j j (𝟙 Y) sq
  simpa only [sfMateIso, sfIntrinsicDerivedPullbackId] using
    dSquare_id_inverse (sfIntrinsicExtensionByZero j A) (sfIntrinsicPullback A (𝟙 U))
      (sfIntrinsicPullback A (𝟙 Y)) (asIso (sfIntrinsicOpenMate A (𝟙 U) j j (𝟙 Y) sq.w))
      (sfIntrinsicPullbackId A U) (sfIntrinsicPullbackId A Y) (sfMate_horizontal_id A j sq.w)

private theorem sfDerivedMate_vertical_id {X Y : Scheme.{u}} (g : X ⟶ Y)
    (sq : IsPullback g (𝟙 X) (𝟙 Y) g) :
    (sfMateIso A g (𝟙 X) (𝟙 Y) g sq).hom =
      whiskerLeft (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedOpenId A X).hom ≫
      whiskerRight (sfIntrinsicDerivedOpenId A Y).inv (sfIntrinsicDerivedPullback A g) := by
  have := sfOpenMate_isIso A g (𝟙 X) (𝟙 Y) g sq
  have hq (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
      (sfIntrinsicOpenMate A g (𝟙 X) (𝟙 Y) g sq.w).app M ≫
        (sfIntrinsicPullback A g).map ((sfIntrinsicOpenId A Y).hom.app M) =
      (sfIntrinsicOpenId A X).hom.app ((sfIntrinsicPullback A g).obj M) := by
    rw [sfMate_vertical_id A g sq.w]
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc,
      ← (sfIntrinsicPullback A g).map_comp, Iso.inv_hom_id_app]
    erw [(sfIntrinsicPullback A g).map_id, Category.comp_id]
  simpa only [sfMateIso, sfIntrinsicDerivedOpenId] using
    dSquare_id_hom (sfIntrinsicPullback A g) (sfIntrinsicExtensionByZero (𝟙 Y) A)
    (sfIntrinsicExtensionByZero (𝟙 X) A) (asIso (sfIntrinsicOpenMate A g (𝟙 X) (𝟙 Y) g sq.w))
    (sfIntrinsicOpenId A Y) (sfIntrinsicOpenId A X) hq

private noncomputable def sfExchangeData : SfOpenSquareExchangeData A where
  exchange := sfExchange A
  canonical := by
    intro U' U Y' Y gU j' j g _ _ sq
    exact sfExchange_canonical A gU j' j g sq
  restriction := sfRestriction A
  horizontal_id := by
    intro U Y j _ sq
    simp only [sfExchange_hom]
    apply inverseTwo _
      (isoWhiskerRight (sfIntrinsicDerivedPullbackId A U) (sfIntrinsicDerivedOpen A j))
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackId A Y))
    simpa only [isoWhiskerLeft_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_inv, isoWhiskerRight_inv] using sfDerivedMate_horizontal_id A j sq
  vertical_id := by
    intro X Y g sq
    simp only [sfExchange_hom]
    apply inverseTwo _
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A g) (sfIntrinsicDerivedOpenId A X))
      (isoWhiskerRight (sfIntrinsicDerivedOpenId A Y) (sfIntrinsicDerivedPullback A g))
    simpa only [isoWhiskerLeft_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_inv, isoWhiskerRight_inv] using sfDerivedMate_vertical_id A g sq
  horizontal_pasting := by
    intro U'' U' U Y'' Y' Y gU hU j j' j'' g h _ _ _ sq sq' outer
    simp only [sfExchange_hom]
    apply inverseFour _
      (isoWhiskerRight (sfIntrinsicDerivedPullbackComp A hU gU)
          (sfIntrinsicDerivedOpen A j''))
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A gU)
          (sfMateIso A hU j'' j' h sq'))
      (isoWhiskerRight (sfMateIso A gU j' j g sq)
          (sfIntrinsicDerivedPullback A h))
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A j) (sfIntrinsicDerivedPullbackComp A h g))
    simpa only [isoWhiskerLeft_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_inv, isoWhiskerRight_inv, Iso.symm_hom, Iso.symm_inv] using
      sfDerivedMate_horizontal A gU hU j j' j'' g h sq sq' outer
  vertical_pasting := by
    intro V' V U' U Y' Y i i' j j' gV gU g _ _ _ _ sq sq' outer
    simp only [sfExchange_hom]
    apply inverseFour _
      (isoWhiskerLeft (sfIntrinsicDerivedPullback A gV) (sfIntrinsicDerivedOpenComp A i' j'))
      (isoWhiskerRight
          (sfMateIso A gV i' i gU sq')
          (sfIntrinsicDerivedOpen A j'))
      (isoWhiskerLeft (sfIntrinsicDerivedOpen A i)
          (sfMateIso A gU j' j g sq))
      (isoWhiskerRight (sfIntrinsicDerivedOpenComp A i j) (sfIntrinsicDerivedPullback A g))
    simpa only [isoWhiskerLeft_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_inv, isoWhiskerRight_inv, Iso.symm_hom, Iso.symm_inv] using
      sfDerivedMate_vertical A i i' j j' gV gU g sq sq' outer

/-- Canonical open-square exchange with finite coefficient ring `A_{E,n}`. -/
theorem proEtale_openSquareExchange (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (@SfOpenSquareExchangeData (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)) := by
  let := Padic.finite_coefficientExtensionRing l E n hn
  exact ⟨sfExchangeData (Padic.coefficientExtensionRing l E n)⟩

end AlgebraicGeometry.Scheme
