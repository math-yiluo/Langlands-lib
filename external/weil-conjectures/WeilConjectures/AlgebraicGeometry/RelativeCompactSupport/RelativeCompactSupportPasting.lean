/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit

/-!
# Horizontal pasting for compactification-relative exchange

## References

* Stacks Project, Tags 0E47 and 09AE
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Replaying the sectionwise localization transports for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open StrictTower
variable (B : Type (u + 1)) [CommRing B]

/-- The recorded exact ordinary module pullback, without changing its presentation. -/
noncomputable abbrev ordinaryG {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (modulePullback B f).mapDerivedCategory

/-- The source pullback compositor, with its K-flat and ordinary-unit normalization. -/
noncomputable def sourceGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryG B (f ≫ g) ≅ ordinaryG B g ⋙ ordinaryG B f :=
  eqToIso (congrArg
    (fun c ↦ Scheme.proEtaleRingDerivedPullback (f ≫ g)
      (coefficients B Z) (coefficients B X) c) (constantRingIso_comp B f g)) ≪≫
    Scheme.proEtaleCanonicalPullbackComposition f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f)

/-- The source square built from the specified derived pullback compositors. -/
noncomputable def sourceSquare {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ordinaryG B i ⋙ ordinaryG B r ≅ ordinaryG B p ⋙ ordinaryG B k :=
  (sourceGComp B r i).symm ≪≫
    eqToIso (congrArg (ordinaryG B) h.symm) ≪≫ sourceGComp B k p

/-- The compactification exchange map for a finite constant coefficient ring: the mate
`Ex_(*,p)(j_! K)` of the derived pullback square for the proper factor, followed by
`Rp'_*(β_K)` for the open factor (`singleBeta`). -/
noncomputable def finiteChosenExchange [Finite B]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z) :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (moduleJ B c.i).mapDerivedCategory (moduleJ B c'.i).mapDerivedCategory
    (ordinaryG B c.g) (moduleDirectImage B c.g).rightDerivedFunctor
    (Scheme.proEtaleRingModuleAdjunction c.g (coefficients B Y)
      (coefficients B c.Z) (constantRingIso B c.g)).mapDerivedCategoryRightDerivedAdjunction
    (ordinaryG B c'.g) (moduleDirectImage B c'.g).rightDerivedFunctor
    (Scheme.proEtaleRingModuleAdjunction c'.g (coefficients B Y')
      (coefficients B c'.Z) (constantRingIso B c'.g)).mapDerivedCategoryRightDerivedAdjunction
    (ordinaryG B a) (ordinaryG B x) (ordinaryG B z)
    (sourceSquare B z c'.g c.g a sp.w) (singleBeta B x c'.i c.i z sj.w sj)

end AlgebraicGeometry.ProEtale.ConstantCompactificationExchange

namespace AlgebraicGeometry.ProEtale.RelativeCompactSupport

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunctionNormalized
  Scheme.proEtaleRingModuleUnitSection Scheme.proEtaleRingCompositeCoefficients
  Scheme.proEtaleRingDerivedPullbackFactors CochainComplex.IsAcyclicTensorKFlat
  SheafOfModules.IsFlatOnSite Scheme.proEtaleRingDirectImageMap

open StrictTower ConstantCompactificationExchange

variable (B : Type (u + 1)) [CommRing B]

/-- Ordinary total right derived direct image, with its recorded module action. -/
noncomputable abbrev ordinaryR {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (moduleDirectImage B f).rightDerivedFunctor

/-- Ordinary exact extension by zero from the recorded open adjunction. -/
noncomputable abbrev ordinaryJ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (moduleJ B j).mapDerivedCategory

/-- The ordinary derived adjunction induced by the specified module adjunction. -/
noncomputable abbrev ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).mapDerivedCategoryRightDerivedAdjunction

/-- The ordinary compositor descends the section-normalized module compositor. -/
noncomputable def ordinaryGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ordinaryG B (f ≫ g) ≅ ordinaryG B g ⋙ ordinaryG B f :=
  Functor.mapDerivedCategoryNatIso (moduleGComp B f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (modulePullback B g) (modulePullback B f)).symm

/-- The ordinary exchange is the unit--square--counit mate of the specified square. -/
noncomputable def ordinaryE {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ordinaryR B p ⋙ ordinaryG B i ⟶ ordinaryG B k ⋙ ordinaryR B r :=
  mateEquiv (ordinaryAdj B p) (ordinaryAdj B r)
    (Functor.mapDerivedCategorySquareIso (moduleSquareG B k r p i h)).hom

attribute [local instance] fixedRestriction_full fixedRestriction_faithful

private theorem moduleOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (fixedRestriction B U).Full := fixedRestriction_full B U
  have : (fixedRestriction B U).Faithful := fixedRestriction_faithful B U
  have : (fixedRestriction B X).Faithful := fixedRestriction_faithful B X
  exact unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
    (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A j) (fixedOpen B j)

/-- The specified ordinary inverse open comparison is invertible for arbitrary rings. -/
theorem ordinaryBetaInv_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g) :
    IsIso (singleBetaInv B a j' j g sq.w) := by
  have := moduleOpenUnit_isIso B j
  have := moduleOpenUnit_isIso B j'
  let ff := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g sq.w).app M) := by
    have := (moduleJAdj B j').isIso_counit_app_of_iso
      ((moduleOpenSquare B a j' j g sq).app M)
    dsimp only [Functor.comp_obj] at this
    have : IsIso ((moduleJAdj B j).unit.app M) := inferInstance
    change IsIso (singleBetaInvApp B a j' j g sq.w M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Ordinary open base change, descending the existing open-unit transpose. -/
noncomputable def ordinaryBeta {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g) :
    ordinaryJ B j ⋙ ordinaryG B g ≅ ordinaryG B a ⋙ ordinaryJ B j' :=
  (Functor.mapDerivedCategorySquareIso
    (@asIso _ _ _ _ (singleBetaInv B a j' j g sq.w)
      (ordinaryBetaInv_isIso B a j' j g sq))).symm

/-- The tower compactification-relative exchange, with the two specified factors. -/
noncomputable def towerH {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z) :
    (J B c.i ⋙ R B c.g) ⋙ G B a ⟶
      G B x ⋙ (J B c'.i ⋙ R B c'.g) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J B c.i)
      (mateEquiv (adj B c.g) (adj B c'.g) (squareG B z c'.g c.g a sp.w).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (beta B x c'.i c.i z sj.w sj).hom (R B c'.g) ≫
    (Functor.associator _ _ _).hom

/-- The ordinary compactification-relative exchange, with the two specified factors. -/
noncomputable def ordinaryH
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z) :
    (ordinaryJ B c.i ⋙ ordinaryR B c.g) ⋙ ordinaryG B a ⟶
      ordinaryG B x ⋙ (ordinaryJ B c'.i ⋙ ordinaryR B c'.g) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ordinaryJ B c.i)
      (mateEquiv (ordinaryAdj B c.g) (ordinaryAdj B c'.g)
        (Functor.mapDerivedCategorySquareIso
          (moduleSquareG B z c'.g c.g a sp.w)).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ordinaryBeta B x c'.i c.i z sj).hom (ordinaryR B c'.g) ≫
    (Functor.associator _ _ _).hom

/-- Pasting two specified transformations, inserting the supplied pullback compositors. -/
def paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type w}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    {A₁ : D₀ ⥤ D₁} {A₂ : D₁ ⥤ D₂} {A : D₀ ⥤ D₂}
    {B₁ : C₀ ⥤ C₁} {B₂ : C₁ ⥤ C₂} {BB : C₀ ⥤ C₂}
    (ca : A ≅ A₁ ⋙ A₂) (cb : BB ≅ B₁ ⋙ B₂)
    (t₁ : F₀ ⋙ A₁ ⟶ B₁ ⋙ F₁) (t₂ : F₁ ⋙ A₂ ⟶ B₂ ⋙ F₂) :
    F₀ ⋙ A ⟶ BB ⋙ F₂ :=
  Functor.whiskerLeft F₀ ca.hom ≫
    (TwoSquare.vComp (TwoSquare.mk F₀ B₁ A₁ F₁ t₁)
      (TwoSquare.mk F₁ B₂ A₂ F₂ t₂)) ≫ Functor.whiskerRight cb.inv F₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem mate_paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type w}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {A₁ : C₀ ⥤ C₁} {A₂ : C₁ ⥤ C₂} {A : C₀ ⥤ C₂}
    {B₁ : D₀ ⥤ D₁} {B₂ : D₁ ⥤ D₂} {BB : D₀ ⥤ D₂}
    (ca : A ≅ A₁ ⋙ A₂) (cb : BB ≅ B₁ ⋙ B₂)
    (s₁ : A₁ ⋙ L₁ ≅ L₀ ⋙ B₁) (s₂ : A₂ ⋙ L₂ ≅ L₁ ⋙ B₂)
    (s : A ⋙ L₂ ≅ L₀ ⋙ BB)
    (hs : ∀ M, cb.hom.app (L₀.obj M) ≫ B₂.map (s₁.inv.app M) ≫
      s₂.inv.app (A₁.obj M) = s.inv.app M ≫ L₂.map (ca.hom.app M)) :
    (mateEquiv a₀ a₂ (TwoSquare.mk _ _ _ _ s.hom)) =
      paste ca cb (mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ s₁.hom))
        (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s₂.hom)) := by
  have hh (M : C₀) : L₂.map (ca.hom.app M) ≫ s₂.hom.app (A₁.obj M) ≫
      B₂.map (s₁.hom.app M) = s.hom.app M ≫ cb.hom.app (L₀.obj M) := by
    apply (cancel_epi (s.inv.app M)).1
    rw [← Category.assoc, ← Category.assoc, ← hs]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← B₂.map_comp, Iso.inv_hom_id_app]
    erw [B₂.map_id]
    exact Category.comp_id _
  ext N
  apply (cancel_mono (R₂.map (cb.hom.app N))).1
  simp only [paste, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, TwoSquare.vComp_app, Category.assoc,
    ← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id]
  apply (a₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  dsimp only [TwoSquare.mk]
  erw [a₂.counit_naturality, reassoc_of% (mateEquiv_counit a₀ a₂ (TwoSquare.mk _ _ _ _ s.hom) N)]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  dsimp only [Functor.comp_obj]
  erw [mateEquiv_counit a₁ a₂ (TwoSquare.mk _ _ _ _ s₂.hom) (B₁.obj N)]
  dsimp only [TwoSquare.mk]
  erw [reassoc_of% (s₂.hom.naturality ((mateEquiv a₀ a₁ (TwoSquare.mk _ _ _ _ s₁.hom)).app N))]
  erw [← B₂.map_comp, mateEquiv_counit a₀ a₁ (TwoSquare.mk _ _ _ _ s₁.hom) N, B₂.map_comp]
  change s.hom.app (R₀.obj N) ≫ BB.map (a₀.counit.app N) ≫ cb.hom.app N =
    L₂.map (ca.hom.app (R₀.obj N)) ≫ s₂.hom.app (A₁.obj (R₀.obj N)) ≫
      B₂.map (s₁.hom.app (R₀.obj N)) ≫ B₂.map (B₁.map (a₀.counit.app N))
  rw [reassoc_of% (hh (R₀.obj N))]
  exact congrArg (fun t ↦ s.hom.app (R₀.obj N) ≫ t)
    (cb.hom.naturality (a₀.counit.app N))

private def combine
    {C C' D D' E E' : Type w}
    [Category.{v} C] [Category.{v} C'] [Category.{v} D] [Category.{v} D']
    [Category.{v} E] [Category.{v} E']
    {J₀ : C ⥤ D} {J₁ : C' ⥤ D'} {P₀ : D ⥤ E} {P₁ : D' ⥤ E'}
    {X : C ⥤ C'} {Z : D ⥤ D'} {A : E ⥤ E'}
    (β : J₀ ⋙ Z ⟶ X ⋙ J₁) (e : P₀ ⋙ A ⟶ Z ⋙ P₁) :
    (J₀ ⋙ P₀) ⋙ A ⟶ X ⋙ (J₁ ⋙ P₁) :=
  (TwoSquare.hComp (TwoSquare.mk _ _ _ _ β) (TwoSquare.mk _ _ _ _ e))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem combine_paste
    {C₀ C₁ C₂ D₀ D₁ D₂ E₀ E₁ E₂ : Type w}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
    [Category.{v} E₀] [Category.{v} E₁] [Category.{v} E₂]
    {J₀ : C₀ ⥤ D₀} {J₁ : C₁ ⥤ D₁} {J₂ : C₂ ⥤ D₂}
    {P₀ : D₀ ⥤ E₀} {P₁ : D₁ ⥤ E₁} {P₂ : D₂ ⥤ E₂}
    {X₁ : C₀ ⥤ C₁} {X₂ : C₁ ⥤ C₂} {X : C₀ ⥤ C₂}
    {Z₁ : D₀ ⥤ D₁} {Z₂ : D₁ ⥤ D₂} {Z : D₀ ⥤ D₂}
    {A₁ : E₀ ⥤ E₁} {A₂ : E₁ ⥤ E₂} {A : E₀ ⥤ E₂}
    (cx : X ≅ X₁ ⋙ X₂) (cz : Z ≅ Z₁ ⋙ Z₂) (ca : A ≅ A₁ ⋙ A₂)
    (β₁ : J₀ ⋙ Z₁ ⟶ X₁ ⋙ J₁) (β₂ : J₁ ⋙ Z₂ ⟶ X₂ ⋙ J₂)
    (e₁ : P₀ ⋙ A₁ ⟶ Z₁ ⋙ P₁) (e₂ : P₁ ⋙ A₂ ⟶ Z₂ ⋙ P₂) :
    combine (paste cz cx β₁ β₂) (paste ca cz e₁ e₂) =
      paste ca cx (combine β₁ e₁) (combine β₂ e₂) := by
  ext M
  simp only [combine, paste, TwoSquare.hComp_app, TwoSquare.vComp_app,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [← P₂.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P₂.map_id, Category.id_comp]
  rw [← reassoc_of% (e₂.naturality (β₁.app M))]

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryGComp_coherence {X Y Z W : Scheme.{u}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : DerivedCategory.{u + 2} (Modules B X)) :
    (ordinaryGComp B j (h ≫ k)).hom.app M ≫
        (ordinaryG B j).map ((ordinaryGComp B h k).hom.app M) =
      (eqToIso (congrArg (ordinaryG B) (Category.assoc j h k).symm)).hom.app M ≫
        (ordinaryGComp B (j ≫ h) k).hom.app M ≫
        (ordinaryGComp B j h).hom.app ((ordinaryG B k).obj M) := by
  have ho : moduleGComp B j (h ≫ k) ≪≫
        Functor.isoWhiskerRight (moduleGComp B h k) (modulePullback B j) =
      eqToIso (congrArg (modulePullback B) (Category.assoc j h k).symm) ≪≫
        moduleGComp B (j ≫ h) k ≪≫
        Functor.isoWhiskerLeft (modulePullback B k) (moduleGComp B j h) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using ordinary_coherence j h k B N
  have hd := descend_coherence.{u + 2, u + 2, u + 2, u + 2, u + 1, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2, u + 2}
    (C := Modules B X) (D := Modules B Y) (E := Modules B Z) (B := Modules B W)
    (modulePullback B k) (modulePullback B h)
    (modulePullback B j) (modulePullback B (h ≫ k)) (modulePullback B (j ≫ h))
    (modulePullback B (j ≫ h ≫ k)) (modulePullback B ((j ≫ h) ≫ k))
    (moduleGComp B h k) (moduleGComp B j h)
    (moduleGComp B j (h ≫ k)) (moduleGComp B (j ≫ h) k)
    (eqToIso (congrArg (modulePullback B) (Category.assoc j h k).symm)) ho
  have he := derived_eqToIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := Modules B X) (D := Modules B W)
    (congrArg (modulePullback B) (Category.assoc j h k).symm)
    (congrArg (ordinaryG B) (Category.assoc j h k).symm)
  rw [he] at hd
  simpa only [ordinaryGComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    using NatTrans.congr_app hd M

private noncomputable def ordinaryGCompEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    ordinaryG B h ≅ ordinaryG B g ⋙ ordinaryG B f :=
  eqToIso (congrArg (ordinaryG B) w.symm) ≪≫ ordinaryGComp B f g

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryGCompEq_coherence {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    ordinaryGCompEq B a bc abc hr ≪≫
        Functor.isoWhiskerRight (ordinaryGCompEq B b c bc hbc) (ordinaryG B a) =
      ordinaryGCompEq B ab c abc hl ≪≫
        Functor.isoWhiskerLeft (ordinaryG B c) (ordinaryGCompEq B a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  ext M
  simpa only [ordinaryGCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using ordinaryGComp_coherence B a b c M

private theorem ordinaryGCompEq_refl {V W S : Scheme.{u}} (f : V ⟶ W) (k : W ⟶ S) :
    ordinaryGComp B f k = ordinaryGCompEq B f k (f ≫ k) rfl := by
  unfold ordinaryGCompEq
  exact (Iso.refl_trans _).symm

private noncomputable def ordinarySquare {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) : ordinaryG B i ⋙ ordinaryG B r ≅
      ordinaryG B p ⋙ ordinaryG B k :=
  Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
    u + 2, u + 2, u + 2, u + 1, u + 1, u + 1, u + 1, u + 2}
      (moduleSquareG B k r p i w)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinarySquare_eq {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) : ordinarySquare B k r p i w =
      (ordinaryGCompEq B r i (k ≫ p) w.symm).symm ≪≫
        ordinaryGCompEq B k p (k ≫ p) rfl := by
  apply Iso.ext
  rw [ordinarySquare, moduleSquareG_eq]
  rw [derivedSquare_comp.{u + 2, u + 2, u + 2, u + 2, u + 1, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2, u + 2}
    (C := Modules B T) (A := Modules B S) (A' := Modules B W) (D := Modules B V)
    (modulePullback B i) (modulePullback B r)
    (modulePullback B p) (modulePullback B k) (modulePullback B (r ≫ i))
    (modulePullback B (k ≫ p)) (moduleGComp B r i) (moduleGComp B k p)
    (congrArg (modulePullback B) w.symm) (congrArg (ordinaryG B) w.symm)]
  exact congrArg Iso.hom (normalizeIsoSquare (ordinaryGComp B r i)
    (ordinaryGComp B k p) (congrArg (ordinaryG B) w.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem ordinarySquare_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : DerivedCategory.{u + 2} (Modules B X)) :
    (ordinaryGComp B b a).hom.app ((ordinaryG B j).obj N) ≫
        (ordinaryG B b).map ((ordinarySquare B a j₁ j g w₁).inv.app N) ≫
        (ordinarySquare B b j₂ j₁ h w₂).inv.app ((ordinaryG B g).obj N) =
      (ordinarySquare B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (ordinaryG B j₂).map ((ordinaryGComp B h g).hom.app N) := by
  rw [ordinaryGCompEq_refl B b a, ordinaryGCompEq_refl B h g,
    ordinarySquare_eq B a j₁ j g w₁, ordinarySquare_eq B b j₂ j₁ h w₂,
    ordinarySquare_eq B (b ≫ a) j₂ j (h ≫ g) w]
  simp only [Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have first := NatTrans.congr_app (congrArg Iso.hom
    (ordinaryGCompEq_coherence B b a j (b ≫ a) (a ≫ j) ((b ≫ a) ≫ j)
      rfl rfl rfl (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at first
  have first' := rearrange_square _ _ _ _ first.symm
  rw [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at first'
  rw [reassoc_of% first']
  have second := NatTrans.congr_app (congrArg Iso.hom
    (ordinaryGCompEq_coherence B b j₁ g (b ≫ j₁) (a ≫ j) ((b ≫ a) ≫ j) rfl w₁.symm
      (by rw [Category.assoc, ← w₁, ← Category.assoc]) (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at second
  have second' := rearrange_square _ _ _ _ second
  simp only [NatIso.inv_hom_app] at second'
  rw [reassoc_of% second']
  rw [Iso.hom_inv_id_app_assoc]
  have key := NatTrans.congr_app (congrArg Iso.hom
    (ordinaryGCompEq_coherence B j₂ h g (b ≫ j₁) (h ≫ g) ((b ≫ a) ≫ j)
      w₂.symm rfl (by rw [Category.assoc, ← w₁, ← Category.assoc]) w.symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [← key]

private noncomputable abbrev ordinaryJAdj {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :=
  exactAdj.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := Modules B U) (D := Modules B X) (moduleJAdj B j)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryBetaInv_unit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g)
    (M : DerivedCategory.{u + 2} (Modules B U)) :
    (ordinaryJAdj B j').unit.app ((ordinaryG B a).obj M) ≫
        (ordinaryG B j').map ((ordinaryBeta B a j' j g sq).inv.app M) =
      (ordinaryG B a).map ((ordinaryJAdj B j).unit.app M) ≫
        (ordinarySquare B a j' j g sq.w).inv.app ((ordinaryJ B j).obj M) := by
  let e := @asIso _ _ _ _ (singleBetaInv B a j' j g sq.w)
    (ordinaryBetaInv_isIso B a j' j g sq)
  have hm (K : Modules B U) :
      (moduleJAdj B j').unit.app ((modulePullback B a).obj K) ≫
          (modulePullback B j').map (e.hom.app K) =
        (modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
          (moduleSquareG B a j' j g sq.w).inv.app ((moduleJ B j).obj K) := by
    simpa only [e, asIso_hom, singleBetaInv, singleBetaInvApp,
      Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
      ((moduleJAdj B j').homEquiv ((modulePullback B a).obj K)
        ((modulePullback B g).obj ((moduleJ B j).obj K))).apply_symm_apply
        ((modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
          (moduleSquareG B a j' j g sq.w).inv.app ((moduleJ B j).obj K))
  have he := exact_mate
    (C₁ := Modules B U) (D₁ := Modules B X)
    (C₂ := Modules B U') (D₂ := Modules B X')
    (moduleJAdj B j) (moduleJAdj B j')
    (moduleSquareG B a j' j g sq.w).symm e (ordinaryJAdj B j) (ordinaryJAdj B j')
    (exactAdj_unit (moduleJAdj B j)) (exactAdj_unit (moduleJAdj B j')) hm M
  simpa only [ordinaryBeta, ordinarySquare, e, Iso.symm_inv,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc] using he

private theorem transposed_pasting
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {A : C₀ ⥤ C₁} {B : C₁ ⥤ C₂} {C : C₀ ⥤ C₂}
    {F : D₀ ⥤ D₁} {H : D₁ ⥤ D₂} {K : D₀ ⥤ D₂}
    (c : C ⟶ A ⋙ B) (d : K ⟶ F ⋙ H)
    (t₁ : R₀ ⋙ A ⟶ F ⋙ R₁) (t₂ : R₁ ⋙ B ⟶ H ⋙ R₂)
    (t : R₀ ⋙ C ⟶ K ⋙ R₂)
    (v₁ : A ⋙ L₁ ⟶ L₀ ⋙ F) (v₂ : B ⋙ L₂ ⟶ L₁ ⋙ H)
    (v : C ⋙ L₂ ⟶ L₀ ⋙ K)
    (h₁ : ∀ M, a₁.unit.app (A.obj M) ≫ R₁.map (v₁.app M) =
      A.map (a₀.unit.app M) ≫ t₁.app (L₀.obj M))
    (h₂ : ∀ M, a₂.unit.app (B.obj M) ≫ R₂.map (v₂.app M) =
      B.map (a₁.unit.app M) ≫ t₂.app (L₁.obj M))
    (hv : ∀ M, a₂.unit.app (C.obj M) ≫ R₂.map (v.app M) =
      C.map (a₀.unit.app M) ≫ t.app (L₀.obj M))
    (ht : ∀ N, c.app (R₀.obj N) ≫ B.map (t₁.app N) ≫ t₂.app (F.obj N) =
      t.app N ≫ R₂.map (d.app N)) (M : C₀) :
    L₂.map (c.app M) ≫ v₂.app (A.obj M) ≫ H.map (v₁.app M) =
      v.app M ≫ d.app (L₀.obj M) := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (a₂.unit.naturality (c.app M))]
  rw [reassoc_of% (h₂ (A.obj M)), reassoc_of% (hv M)]
  erw [← t₂.naturality (v₁.app M)]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← Category.assoc (B.map _), ← B.map_comp, h₁ M, B.map_comp]
  rw [Category.assoc, ← reassoc_of% (c.naturality (a₀.unit.app M))]
  rw [ht]

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryBeta_comp {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g))
    (s₁ : IsPullback a j₁ j g) (s₂ : IsPullback b j₂ j₁ h)
    (s : IsPullback (b ≫ a) j₂ j (h ≫ g)) (M : DerivedCategory.{u + 2} (Modules B U)) :
    (ordinaryGComp B h g).hom.app ((ordinaryJ B j).obj M) ≫
        (ordinaryG B h).map ((ordinaryBeta B a j₁ j g s₁).hom.app M) ≫
        (ordinaryBeta B b j₂ j₁ h s₂).hom.app ((ordinaryG B a).obj M) =
      (ordinaryBeta B (b ≫ a) j₂ j (h ≫ g) s).hom.app M ≫
        (ordinaryJ B j₂).map ((ordinaryGComp B b a).hom.app M) := by
  let e₁ := ordinaryBeta B a j₁ j g s₁
  let e₂ := ordinaryBeta B b j₂ j₁ h s₂
  let e := ordinaryBeta B (b ≫ a) j₂ j (h ≫ g) s
  have hInv : (ordinaryJ B j₂).map ((ordinaryGComp B b a).hom.app M) ≫
      e₂.inv.app ((ordinaryG B a).obj M) ≫ (ordinaryG B h).map (e₁.inv.app M) =
        e.inv.app M ≫ (ordinaryGComp B h g).hom.app ((ordinaryJ B j).obj M) := by
    exact transposed_pasting (ordinaryJAdj B j) (ordinaryJAdj B j₁) (ordinaryJAdj B j₂)
      (ordinaryGComp B b a).hom (ordinaryGComp B h g).hom
      (ordinarySquare B a j₁ j g w₁).inv (ordinarySquare B b j₂ j₁ h w₂).inv
      (ordinarySquare B (b ≫ a) j₂ j (h ≫ g) w).inv
      (ordinaryBeta B a j₁ j g s₁).inv (ordinaryBeta B b j₂ j₁ h s₂).inv
      (ordinaryBeta B (b ≫ a) j₂ j (h ≫ g) s).inv
      (ordinaryBetaInv_unit B a j₁ j g s₁) (ordinaryBetaInv_unit B b j₂ j₁ h s₂)
      (ordinaryBetaInv_unit B (b ≫ a) j₂ j (h ≫ g) s)
      (ordinarySquare_pasting_inv B j j₁ j₂ g h a b w₁ w₂ w) M
  change _ ≫ (ordinaryG B h).map (e₁.hom.app M) ≫ e₂.hom.app _ =
    e.hom.app M ≫ _
  apply (cancel_epi (e.inv.app M)).1
  rw [← Category.assoc, ← Category.assoc, ← hInv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(ordinaryG B h).map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The three horizontal-pasting equalities in the ordinary derived categories. -/
theorem ordinaryPasting {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (c₀ : Compactification f₀) (c₁ : Compactification f₁) (c₂ : Compactification f₂)
    [QuasiCompact c₀.i]
    (a : Y₁ ⟶ Y₀) (b : Y₂ ⟶ Y₁)
    (x₁ : X₁ ⟶ X₀) (x₂ : X₂ ⟶ X₁)
    (z₁ : c₁.Z ⟶ c₀.Z) (z₂ : c₂.Z ⟶ c₁.Z)
    (sp₁ : IsPullback z₁ c₁.g c₀.g a) (sp₂ : IsPullback z₂ c₂.g c₁.g b)
    (sj₁ : IsPullback x₁ c₁.i c₀.i z₁) (sj₂ : IsPullback x₂ c₂.i c₁.i z₂) :
    (ordinaryE B (z₂ ≫ z₁) c₂.g c₀.g (b ≫ a) (sp₂.paste_horiz sp₁).w =
      paste (ordinaryGComp B b a) (ordinaryGComp B z₂ z₁)
        (ordinaryE B z₁ c₁.g c₀.g a sp₁.w) (ordinaryE B z₂ c₂.g c₁.g b sp₂.w)) ∧
    ((ordinaryBeta B (x₂ ≫ x₁) c₂.i c₀.i (z₂ ≫ z₁) (sj₂.paste_horiz sj₁)).hom =
      paste (ordinaryGComp B z₂ z₁) (ordinaryGComp B x₂ x₁)
        ((ordinaryBeta B x₁ c₁.i c₀.i z₁ sj₁).hom) ((ordinaryBeta B x₂ c₂.i c₁.i z₂ sj₂).hom)) ∧
    (ordinaryH B c₀ c₂ (b ≫ a) (x₂ ≫ x₁) (z₂ ≫ z₁) (sp₂.paste_horiz sp₁) (sj₂.paste_horiz sj₁) =
      paste (ordinaryGComp B b a) (ordinaryGComp B x₂ x₁)
        (ordinaryH B c₀ c₁ a x₁ z₁ sp₁ sj₁)
        (ordinaryH B c₁ c₂ b x₂ z₂ sp₂ sj₂)) := by
  have he : ordinaryE B (z₂ ≫ z₁) c₂.g c₀.g (b ≫ a) (sp₂.paste_horiz sp₁).w =
      paste (ordinaryGComp B b a) (ordinaryGComp B z₂ z₁)
        (ordinaryE B z₁ c₁.g c₀.g a sp₁.w) (ordinaryE B z₂ c₂.g c₁.g b sp₂.w) := by
    exact mate_paste (ordinaryAdj B c₀.g) (ordinaryAdj B c₁.g) (ordinaryAdj B c₂.g)
      (ordinaryGComp B b a) (ordinaryGComp B z₂ z₁)
      (ordinarySquare B z₁ c₁.g c₀.g a sp₁.w) (ordinarySquare B z₂ c₂.g c₁.g b sp₂.w)
      (ordinarySquare B (z₂ ≫ z₁) c₂.g c₀.g (b ≫ a) (sp₂.paste_horiz sp₁).w)
      (ordinarySquare_pasting_inv B c₀.g c₁.g c₂.g a b z₁ z₂
        sp₁.w sp₂.w (sp₂.paste_horiz sp₁).w)
  have hb : (ordinaryBeta B (x₂ ≫ x₁) c₂.i c₀.i (z₂ ≫ z₁)
        (sj₂.paste_horiz sj₁)).hom =
      paste (ordinaryGComp B z₂ z₁) (ordinaryGComp B x₂ x₁)
        (ordinaryBeta B x₁ c₁.i c₀.i z₁ sj₁).hom
        (ordinaryBeta B x₂ c₂.i c₁.i z₂ sj₂).hom := by
    ext M
    apply (cancel_mono ((ordinaryJ B c₂.i).map ((ordinaryGComp B x₂ x₁).hom.app M))).1
    simp only [paste, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, TwoSquare.vComp_app, TwoSquare.mk,
      Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
    exact (ordinaryBeta_comp B c₀.i c₁.i c₂.i z₁ z₂ x₁ x₂ sj₁.w sj₂.w
      (sj₂.paste_horiz sj₁).w sj₁ sj₂ (sj₂.paste_horiz sj₁) M).symm
  refine ⟨he, hb, ?_⟩
  change combine (ordinaryBeta B (x₂ ≫ x₁) c₂.i c₀.i (z₂ ≫ z₁)
      (sj₂.paste_horiz sj₁)).hom
    (ordinaryE B (z₂ ≫ z₁) c₂.g c₀.g (b ≫ a) (sp₂.paste_horiz sp₁).w) = _
  rw [he, hb]
  exact combine_paste (ordinaryGComp B x₂ x₁) (ordinaryGComp B z₂ z₁)
    (ordinaryGComp B b a) _ _ _ _

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleRingModulePullback
  Scheme.proEtaleCanonicalPullbackComposition Scheme.proEtaleConstantRingComparison

private theorem ordinaryBeta_eq_singleBeta [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g) :
    ordinaryBeta B a j' j g sq = singleBeta B a j' j g sq.w sq := by
  rw [singleBeta_lift]
  apply Iso.ext
  simp only [ordinaryBeta, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The evaluation comparison for the specified compact-support composite. -/
noncomputable def supportEval {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    (J B c.i ⋙ R B c.g) ⋙ ev B Y n ≅
      ev B X n ⋙ (ordinaryJ B c.i ⋙ ordinaryR B c.g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J B c.i)
      (@asIso _ _ _ _ (evalR B c.g n) (evalR_isIso B c.g n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (evalJ B c.i n) (ordinaryR B c.g) ≪≫
    Functor.associator _ _ _

private theorem mapped_combine
    {D E D' E' : Type w}
    [Category.{v} D] [Category.{v} E] [Category.{v} D'] [Category.{v} E']
    {F : D ⥤ E} {T : D ⥤ D'} {U : E ⥤ E'} {F' : D' ⥤ E'}
    (δ : F ⋙ U ⟶ T ⋙ F') {Q Q' : D} {V V' Z Z' : D'}
    (β : Q ⟶ Q') (j : T.obj Q' ⟶ V) (x : V ⟶ V')
    (z : T.obj Q ⟶ Z) (m : Z ⟶ Z') (β' : Z' ⟶ V')
    {L A B C : E'} (e : L ⟶ U.obj (F.obj Q))
    (a : L ⟶ A) (b : A ⟶ B) (h : B ⟶ C)
    (c : B ⟶ F'.obj Z) (c' : C ⟶ F'.obj Z')
    (he : e ≫ δ.app Q ≫ F'.map z = a ≫ b ≫ c)
    (hb : T.map β ≫ j ≫ x = z ≫ m ≫ β')
    (hn : c ≫ F'.map m = h ≫ c') :
    e ≫ U.map (F.map β) ≫ δ.app Q' ≫ F'.map j ≫ F'.map x =
      a ≫ b ≫ h ≫ c' ≫ F'.map β' := by
  rw [reassoc_of% (δ.naturality β)]
  rw [← F'.map_comp, ← F'.map_comp, hb, F'.map_comp, F'.map_comp]
  rw [reassoc_of% he, reassoc_of% hn]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem evaluation_exchange {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) (N : Derived B W) (n : ℕ) :
    (ev B S n).map ((exchange B k r p i w).app N) ≫
        (evalR B r n).app ((G B k).obj N) ≫
        (ordinaryR B r).map ((evalG B k n).hom.app N) =
      (evalG B i n).hom.app ((R B p).obj N) ≫
        (ordinaryG B i).map ((evalR B p n).app N) ≫
        (ordinaryE B k r p i w).app ((ev B W n).obj N) := by
  have hc (M : Derived B T) :
      (ev B V n).map ((squareG B k r p i w).hom.app M) ≫
          (evalG B k n).hom.app ((G B p).obj M) ≫
          (ordinaryG B k).map ((evalG B p n).hom.app M) =
        (evalG B r n).hom.app ((G B i).obj M) ≫
          (ordinaryG B r).map ((evalG B i n).hom.app M) ≫
          (ordinarySquare B k r p i w).hom.app ((ev B T n).obj M) := by
    rw [squareG_lift B k r p i w]
    have he := evalD_square.{u + 2, u + 2, u + 2, u + 2, u + 1, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2, u + 2, u + 2, u + 2, u + 2, u + 2}
      (C := Modules B T) (A := Modules B S) (A' := Modules B W) (D := Modules B V)
      (modulePullback B i) (modulePullback B r)
      (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i w) M n
    rw [← evalG_eq B i n, ← evalG_eq B r n,
      ← evalG_eq B p n, ← evalG_eq B k n] at he
    exact he
  symm
  exact CategoryTheory.Adjunction.coefficient_exchange_of_counit
    (adj B p) (adj B r) (ordinaryAdj B p) (ordinaryAdj B r)
    (squareG B k r p i w).hom (ordinarySquare B k r p i w).hom
    (exchange B k r p i w) (ordinaryE B k r p i w)
    (mateEquiv_counit (adj B p) (adj B r) _)
    (by
      intro K
      exact mateEquiv_counit (ordinaryAdj B p) (ordinaryAdj B r)
        (Functor.mapDerivedCategorySquareIso (moduleSquareG B k r p i w)).hom K)
    (evalG B p n) (evalG B r n) (evalG B i n).hom (evalG B k n).hom
    (evalR B p n) (evalR B r n)
    (mateEquiv_counit (adj B p) (ordinaryAdj B p) (evalG B p n).inv)
    (mateEquiv_counit (adj B r) (ordinaryAdj B r) (evalG B r n).inv) hc N

/-- Finite evaluation carries E, beta and H to the ordinary specified maps. -/
theorem finiteEvaluation [Finite B] {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (a : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z)
    (sp : IsPullback z c'.g c.g a) (sj : IsPullback x c'.i c.i z)
    (M : Derived B X) (N : Derived B c.Z) (n : ℕ) :
    ((ev B Y' n).map ((exchange B z c'.g c.g a sp.w).app N) ≫
        (evalR B c'.g n).app ((G B z).obj N) ≫
        (ordinaryR B c'.g).map ((evalG B z n).hom.app N) =
      (evalG B a n).hom.app ((R B c.g).obj N) ≫
        (ordinaryG B a).map ((evalR B c.g n).app N) ≫
        (ordinaryE B z c'.g c.g a sp.w).app ((ev B c.Z n).obj N)) ∧
    ((ev B c'.Z n).map ((beta B x c'.i c.i z sj.w sj).hom.app M) ≫
        (evalJ B c'.i n).hom.app ((G B x).obj M) ≫
        (ordinaryJ B c'.i).map ((evalG B x n).hom.app M) =
      (evalG B z n).hom.app ((J B c.i).obj M) ≫
        (ordinaryG B z).map ((evalJ B c.i n).hom.app M) ≫
        (ordinaryBeta B x c'.i c.i z sj).hom.app ((ev B X n).obj M)) ∧
    ((ev B Y' n).map ((towerH B c c' a x z sp sj).app M) ≫
        (supportEval B c' n).hom.app ((G B x).obj M) ≫
        (ordinaryJ B c'.i ⋙ ordinaryR B c'.g).map ((evalG B x n).hom.app M) =
      (evalG B a n).hom.app ((J B c.i ⋙ R B c.g).obj M) ≫
        (ordinaryG B a).map ((supportEval B c n).hom.app M) ≫
        (ordinaryH B c c' a x z sp sj).app ((ev B X n).obj M)) := by
  have he := evaluation_exchange B z c'.g c.g a sp.w N n
  have hb : (ev B c'.Z n).map ((beta B x c'.i c.i z sj.w sj).hom.app M) ≫
        (evalJ B c'.i n).hom.app ((G B x).obj M) ≫
        (ordinaryJ B c'.i).map ((evalG B x n).hom.app M) =
      (evalG B z n).hom.app ((J B c.i).obj M) ≫
        (ordinaryG B z).map ((evalJ B c.i n).hom.app M) ≫
        (ordinaryBeta B x c'.i c.i z sj).hom.app ((ev B X n).obj M) := by
    rw [ordinaryBeta_eq_singleBeta]
    exact beta_evaluation B x c'.i c.i z sj.w sj M n
  refine ⟨he, hb, ?_⟩
  have heJ := evaluation_exchange B z c'.g c.g a sp.w ((J B c.i).obj M) n
  have ht : towerH B c c' a x z sp sj =
      combine (beta B x c'.i c.i z sj.w sj).hom
        (exchange B z c'.g c.g a sp.w) := rfl
  have ho : ordinaryH B c c' a x z sp sj =
      combine (ordinaryBeta B x c'.i c.i z sj).hom
        (ordinaryE B z c'.g c.g a sp.w) := rfl
  rw [ht, ho]
  simp only [combine, TwoSquare.hComp, TwoSquare.mk,
    supportEval, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Functor.map_comp,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    asIso_hom, Functor.comp_obj, Functor.comp_map, Category.id_comp,
    Category.comp_id, Category.assoc]
  change (ev B Y' n).map ((exchange B z c'.g c.g a sp.w).app ((J B c.i).obj M)) ≫
      (ev B Y' n).map ((R B c'.g).map ((beta B x c'.i c.i z sj.w sj).hom.app M)) ≫
      (evalR B c'.g n).app ((J B c'.i).obj ((G B x).obj M)) ≫
      (ordinaryR B c'.g).map ((evalJ B c'.i n).hom.app ((G B x).obj M)) ≫
      (ordinaryR B c'.g).map ((ordinaryJ B c'.i).map ((evalG B x n).hom.app M)) =
    (evalG B a n).hom.app ((R B c.g).obj ((J B c.i).obj M)) ≫
      (ordinaryG B a).map ((evalR B c.g n).app ((J B c.i).obj M)) ≫
      (ordinaryG B a).map ((ordinaryR B c.g).map ((evalJ B c.i n).hom.app M)) ≫
      (ordinaryE B z c'.g c.g a sp.w).app ((ordinaryJ B c.i).obj ((ev B X n).obj M)) ≫
      (ordinaryR B c'.g).map
        ((ordinaryBeta B x c'.i c.i z sj).hom.app ((ev B X n).obj M))
  exact mapped_combine (evalR B c'.g n)
    ((beta B x c'.i c.i z sj.w sj).hom.app M)
    ((evalJ B c'.i n).hom.app ((G B x).obj M))
    ((ordinaryJ B c'.i).map ((evalG B x n).hom.app M))
    ((evalG B z n).hom.app ((J B c.i).obj M))
    ((ordinaryG B z).map ((evalJ B c.i n).hom.app M))
    ((ordinaryBeta B x c'.i c.i z sj).hom.app ((ev B X n).obj M))
    ((ev B Y' n).map ((exchange B z c'.g c.g a sp.w).app ((J B c.i).obj M)))
    ((evalG B a n).hom.app ((R B c.g).obj ((J B c.i).obj M)))
    ((ordinaryG B a).map ((evalR B c.g n).app ((J B c.i).obj M)))
    ((ordinaryG B a).map ((ordinaryR B c.g).map ((evalJ B c.i n).hom.app M)))
    ((ordinaryE B z c'.g c.g a sp.w).app ((ev B c.Z n).obj ((J B c.i).obj M)))
    ((ordinaryE B z c'.g c.g a sp.w).app ((ordinaryJ B c.i).obj ((ev B X n).obj M)))
    heJ hb ((ordinaryE B z c'.g c.g a sp.w).naturality ((evalJ B c.i n).hom.app M)).symm

private theorem exchange_congr {V W S T : Scheme.{u}}
    (k k' : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i i' : S ⟶ T)
    (h : k ≫ p = r ≫ i) (h' : k' ≫ p = r ≫ i') (hk : k = k') (hi : i = i') :
    exchange B k r p i h =
      Functor.whiskerLeft (R B p) (eqToHom (congrArg (G B) hi)) ≫
        exchange B k' r p i' h' ≫
        Functor.whiskerRight (eqToHom (congrArg (G B) hk.symm)) (R B r) := by
  subst k' i'
  simp

end AlgebraicGeometry.ProEtale.RelativeCompactSupport
