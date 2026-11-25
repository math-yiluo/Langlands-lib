/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerSquareUnitSections
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-!
# Open-unit normalization of base change on strict constant towers

Source: Stacks Project, Tags 09AE and 04J0; the final coherence sentence of
`thm-cbc-complete-proetale.proof.md`, main-20261015
(blueprint: lem-cbc-tower-open-beta-normalization).

All derived categories are ordinary unbounded derived categories of strict diagrams.
The natural transformations are compared before any derived evaluation is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The specified module inverse-image/direct-image adjunction, without new choices.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⊣ moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)

/-- The restriction/direct-image exchange transformation is the mate of the canonical
inverse-image compositor square; its section normalization is asserted below.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaRestriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) :
    moduleDirectImage B g ⋙ modulePullback B j ⟶
      modulePullback B j' ⋙ moduleDirectImage B a :=
  (mateEquiv (openBetaModuleAdj B g) (openBetaModuleAdj B a)
    (TwoSquare.mk _ _ _ _ (moduleSquareG B a j' j g w).inv))

set_option backward.isDefEq.respectTransparency false in
private theorem openBetaModuleJUnit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
    (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A j) (fixedOpen B j)

/-- The specified inverse open-unit transpose is invertible for arbitrary constant B.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: conjugate the section-normalized right-adjoint comparison under the composite
adjunctions (def-weil-pbc-composite-adjunction,
situation-conventions). The iterated-mate formula
lem-trf-iterated-square-mates identifies its inverse with `singleBetaInv`.
The transpose formula lem-pur-adjunction-mate-transpose gives precisely the pulled-back
open unit, so injectivity of the Hom equivalence proves the identification. -/
theorem openBetaModule_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g w) := by
  have := openBetaModuleJUnit B j
  have := openBetaModuleJUnit B j'
  let fm := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := fm.full
  have := fm.faithful
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g w).app M) := by
    have : IsIso ((moduleJAdj B j').counit.app
        ((modulePullback B g).obj ((moduleJ B j).obj M))) :=
      (moduleJAdj B j').isIso_counit_app_of_iso ((moduleOpenSquare B a j' j g sq).app M)
    change IsIso (singleBetaInvApp B a j' j g w M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The sheaf comparison is the inverse of the prescribed open-unit transpose.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModule {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j' :=
  (@asIso _ _ _ _ (singleBetaInv B a j' j g w)
    (openBetaModule_isIso B a j' j g w sq)).symm

/-- The left-adjoint comparison of the section-normalized restriction is exactly the
open-unit-normalized sheaf comparison, including the specified direction.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: apply conjugate-iso uniqueness to the two composite adjunctions. The iterated
mate identity identifies the resulting inverse with the left open mate of the square
compositor. Apply the mate-transpose identity to the identity of j_!M; its transpose
is the open unit. This proves the formula and its uniqueness. -/
theorem openBetaModule_normalized {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    (conjugateEquiv ((moduleJAdj B j).comp (openBetaModuleAdj B g))
      ((openBetaModuleAdj B a).comp (moduleJAdj B j'))
      (openBetaModule B a j' j g w sq).inv) = openBetaRestriction B a j' j g w ∧
    (∀ M : Modules B U,
      (moduleJAdj B j').homEquiv _ _ ((openBetaModule B a j' j g w sq).inv.app M) =
        (modulePullback B a).map ((moduleJAdj B j).unit.app M) ≫
          (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj M)) := by
  have hm : mateEquiv (moduleJAdj B j) (moduleJAdj B j')
      (TwoSquare.mk _ _ _ _ (singleBetaInv B a j' j g w)) =
        TwoSquare.mk _ _ _ _ (moduleSquareG B a j' j g w).inv := by
    apply mateEquiv_eq_of_unit
    intro M
    symm
    exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _
  constructor
  · change conjugateEquiv _ _ (singleBetaInv B a j' j g w) = _
    rw [← iterated_mateEquiv_conjugateEquiv (moduleJAdj B j) (moduleJAdj B j')
      (openBetaModuleAdj B a) (openBetaModuleAdj B g), hm]
    rfl
  · intro M
    exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] moduleGComp moduleRComp moduleSquareG modulePullback
attribute [local irreducible] constantRingIso

attribute [local irreducible] gComp gId adj jAdj G R J alpha

private theorem moduleGComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (modulePullback B j) (moduleGId B U).hom =
      (eqToIso (congrArg (modulePullback B) (Category.id_comp j))).hom := by
  apply NatTrans.ext
  funext N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((eqToIso
    (congrArg (modulePullback B) (Category.id_comp j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using ordinary_left_unit j B N

private theorem moduleGComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (moduleGId B X).hom (modulePullback B j) =
      (eqToIso (congrArg (modulePullback B) (Category.comp_id j))).hom := by
  apply NatTrans.ext
  funext N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  apply (cancel_epi ((eqToIso
    (congrArg (modulePullback B) (Category.comp_id j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using ordinary_right_unit j B N

private theorem gComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (G B j) (gId B U).hom =
      (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
  apply NatTrans.ext
  funext N
  have h := NatTrans.congr_app (congrArg Iso.hom (gCompEq_left_unit j B)) N
  simp only [gCompEq, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom,
    NatTrans.id_app] at h
  erw [Category.comp_id] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((eqToIso
    (congrArg (G B) (Category.id_comp j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h

private theorem gComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (gId B X).hom (G B j) =
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom := by
  apply NatTrans.ext
  funext N
  have h := NatTrans.congr_app (congrArg Iso.hom (gCompEq_right_unit j B)) N
  simp only [gCompEq, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom,
    NatTrans.id_app] at h
  erw [Category.comp_id ((G B j).map ((gId B X).hom.app N))] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  apply (cancel_epi ((eqToIso
    (congrArg (G B) (Category.comp_id j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h

private theorem squareG_id {U X : Scheme.{u}} (j : U ⟶ X)
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (N : Derived B X) :
    (squareG B (𝟙 U) j j (𝟙 X) h).inv.app N ≫
        (G B j).map ((gId B X).hom.app N) =
      (gId B U).hom.app ((G B j).obj N) := by
  have hl := congr_app (gComp_id_left B j) N
  have hr := congr_app (gComp_id_right B j) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hl hr
  have ht : (eqToIso (congrArg (G B) h)).hom ≫
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom =
        (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htN := congr_app ht N
  simp only [NatTrans.comp_app] at htN
  simp only [squareG, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Category.assoc]
  change (gComp B (𝟙 U) j).inv.app N ≫
      (eqToIso (congrArg (G B) h)).hom.app N ≫
      (gComp B j (𝟙 X)).hom.app N ≫
      (G B j).map ((gId B X).hom.app N) = _
  rw [hr, htN, ← hl]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem betaInv_id_aux
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {G₀ : D ⥤ C} (a : L ⊣ G₀)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (s : H ⋙ G₀ ≅ G₀ ⋙ I)
    (hs : ∀ N, s.inv.app N ≫ G₀.map (eH.hom.app N) = eI.hom.app (G₀.obj N))
    (M : C) :
    (a.homEquiv _ _).symm (I.map (a.unit.app M) ≫ s.inv.app (L.obj M)) ≫
        eH.hom.app (L.obj M) = L.map (eI.hom.app M) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Category.assoc, hs, Adjunction.homEquiv_unit]
  exact (eI.hom.naturality (a.unit.app M)).trans (a.unit.naturality (eI.hom.app M))

private theorem squareG_flip {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    squareG B r k i p h.symm = (squareG B k r p i h).symm := by
  simp only [squareG, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem leftAdjointIdIso_transpose
    {C : Type*} [Category* C] {L G₀ : C ⥤ C} (a : L ⊣ G₀)
    (e : G₀ ≅ 𝟭 C) (N : C) :
    a.unit.app N ≫ G₀.map ((Adjunction.leftAdjointIdIso a e).hom.app N) =
      e.inv.app N := by
  have h := unit_conjugateEquiv Adjunction.id a (Adjunction.leftAdjointIdIso a e).hom N
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp]
    using h.symm

private theorem jId_transpose (X : Scheme.{u}) (N : Derived B X) :
    (jAdj B (𝟙 X)).unit.app N ≫
        (G B (𝟙 X)).map ((jId B X).hom.app N) = (gId B X).inv.app N := by
  exact leftAdjointIdIso_transpose (jAdj B (𝟙 X)) (gId B X) N

private theorem squareG_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (squareG B p (𝟙 U) (𝟙 X) p h).inv.app N ≫
        (gId B U).hom.app ((G B p).obj N) =
      (G B p).map ((gId B X).hom.app N) := by
  rw [squareG_flip B (𝟙 U) p p (𝟙 X) h.symm, Iso.symm_inv]
  apply (cancel_epi ((squareG B (𝟙 U) p p (𝟙 X) h.symm).inv.app N)).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (squareG_id B p h.symm N).symm

private theorem betaInv_id_open_aux
    {C D : Type*} [Category* C] [Category* D]
    {J₀ G₀ : C ⥤ C} {J₁ G₁ : D ⥤ D} (a₀ : J₀ ⊣ G₀) (a₁ : J₁ ⊣ G₁)
    (F : C ⥤ D) (e₀ : G₀ ≅ 𝟭 C) (e₁ : G₁ ≅ 𝟭 D)
    (j₀ : J₀ ≅ 𝟭 C) (j₁ : J₁ ≅ 𝟭 D) (s : F ⋙ G₁ ≅ G₀ ⋙ F)
    (h₀ : ∀ N, a₀.unit.app N ≫ G₀.map (j₀.hom.app N) = e₀.inv.app N)
    (h₁ : ∀ N, a₁.unit.app N ≫ G₁.map (j₁.hom.app N) = e₁.inv.app N)
    (hs : ∀ N, s.inv.app N ≫ e₁.hom.app (F.obj N) = F.map (e₀.hom.app N))
    (N : C) :
    (a₁.homEquiv _ _).symm (F.map (a₀.unit.app N) ≫ s.inv.app (J₀.obj N)) ≫
        F.map (j₀.hom.app N) = j₁.hom.app (F.obj N) := by
  apply (a₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  dsimp only [Functor.id_obj]
  rw [h₁]
  have hn := s.inv.naturality (j₀.hom.app N)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, h₀]
  apply (cancel_mono (e₁.hom.app (F.obj N))).1
  rw [Category.assoc, hs, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (F.map_id _).trans (Iso.inv_hom_id_app e₁ _).symm

private theorem betaInv_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (betaInv B p (𝟙 U) (𝟙 X) p h).app N ≫
        (G B p).map ((jId B X).hom.app N) =
      (jId B U).hom.app ((G B p).obj N) := by
  exact betaInv_id_open_aux (jAdj B (𝟙 X)) (jAdj B (𝟙 U)) (G B p)
    (gId B X) (gId B U) (jId B X) (jId B U)
    (squareG B p (𝟙 U) (𝟙 X) p h) (jId_transpose B X) (jId_transpose B U)
    (squareG_id_open B p h) N

private theorem iso_unit_cancel {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (h : e.inv ≫ a = b) : e.hom ≫ b = a := by
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem beta_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (hsq : IsPullback p (𝟙 U) (𝟙 X) p)
    (N : Derived B X) :
    (beta B p (𝟙 U) (𝟙 X) p h hsq).hom.app N ≫
        (jId B U).hom.app ((G B p).obj N) =
      (G B p).map ((jId B X).hom.app N) := by
  exact iso_unit_cancel ((beta B p (𝟙 U) (𝟙 X) p h hsq).app N) _ _
    (betaInv_id_open B p h N)

attribute [local semireducible] G R J adj jAdj gComp gId alpha
set_option backward.isDefEq.respectTransparency true

/-- Apply the sheaf comparison termwise to the strict inverse system, with its
transition maps retained. Source: Stacks, Tag 09AE
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaTower {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    towerJ B j ⋙ towerPullback B g ≅ towerPullback B a ⋙ towerJ B j' :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ (Modules B U) (Modules B X')).mapIso
      (openBetaModule B a j' j g w sq) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

set_option backward.isDefEq.respectTransparency true in
/-- The derived tower comparison is the exact descent of the specific sheaf comparison,
and its inverse has the specified open-unit transpose before evaluation.
Source: Stacks, Tags 015F, 09AE and 04J0
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: extend the sheaf comparison termwise; naturality gives the transition-map and
chain-map equations. Use situation-conventions and
lem-weil-pbc-localization-universal-property (2),(3) to descend the comparison, its
inverse identities and its transpose equation. The descended units are the specified
jAdj units, so injectivity of their Hom equivalence identifies the result with beta.
No faithfulness of derived evaluations is used. -/
theorem openBetaNormalization {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    beta B a j' j g w sq =
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (openBetaTower B a j' j g w sq) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm ∧
    (∀ M : Derived B U,
      (jAdj B j').homEquiv _ _ ((beta B a j' j g w sq).inv.app M) =
        (G B a).map ((jAdj B j).unit.app M) ≫
          (squareG B a j' j g w).inv.app ((J B j).obj M)) := by
  have hb : betaInv B a j' j g w =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B a) (F₂ := towerJ B j')
        (G₁ := towerJ B j) (G₂ := towerPullback B g)
        (towerSquare (modulePullback B a) (moduleJ B j') (moduleJ B j)
          (modulePullback B g) (openBetaModule B a j' j g w sq).symm)).hom := by
    let e := @asIso _ _ _ _ (singleBetaInv B a j' j g w)
      (openBetaModule_isIso B a j' j g w sq)
    let tw := towerSquare (modulePullback B g) (modulePullback B j')
      (modulePullback B j) (modulePullback B a) (moduleSquareG B a j' j g w)
    have hτ : (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B j) (F₂ := towerPullback B a)
        (G₁ := towerPullback B g) (G₂ := towerPullback B j') tw.symm).hom =
        (squareG B a j' j g w).inv := by
      have he : squareG B a j' j g w = Functor.mapDerivedCategorySquareIso
          (F₁ := towerPullback B g) (F₂ := towerPullback B j')
          (G₁ := towerPullback B j) (G₂ := towerPullback B a) tw :=
        Iso.ext (squareG_lift B a j' j g w)
      rw [he]
      simp only [Functor.mapDerivedCategorySquareIso,
        Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Category.assoc]
    have hm (K : Modules B U) :
        (moduleJAdj B j').unit.app ((modulePullback B a).obj K) ≫
            (modulePullback B j').map (e.hom.app K) =
          (modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
            (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj K) := by
      simpa only [e, asIso_hom, singleBetaInv, singleBetaInvApp,
        Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
        ((moduleJAdj B j').homEquiv ((modulePullback B a).obj K)
          ((modulePullback B g).obj ((moduleJ B j).obj K))).apply_symm_apply
          ((modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
            (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj K))
    apply NatTrans.ext
    funext M
    apply ((jAdj B j').homEquiv ((G B a).obj M)
      ((G B g).obj ((J B j).obj M))).injective
    change (jAdj B j').homEquiv ((G B a).obj M) ((G B g).obj ((J B j).obj M))
      (betaInvApp B a j' j g w M) = _
    rw [betaInvApp, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    symm
    rw [← hτ, ← exactAdj_jAdj B j, ← exactAdj_jAdj B j']
    dsimp only [tw]
    rw [← towerSquare_symm]
    exact exact_mate_tower (C₁ := Modules B U) (D₁ := Modules B X)
      (C₂ := Modules B U') (D₂ := Modules B X')
      (f₁ := moduleJ B j) (g₁ := modulePullback B j)
      (f₂ := moduleJ B j') (g₂ := modulePullback B j')
      (u := modulePullback B a) (v := modulePullback B g)
      (moduleJAdj B j) (moduleJAdj B j') (moduleSquareG B a j' j g w).symm e hm M
  constructor
  · apply Iso.ext_inv
    rw [show (beta B a j' j g w sq).inv = betaInv B a j' j g w from rfl, hb]
    rw [towerSquare_symm]
    have ht : towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B a)
        (moduleJ B j') (openBetaModule B a j' j g w sq) =
          openBetaTower B a j' j g w sq := by
      unfold towerSquare openBetaTower
      rfl
    rw [ht]
    simp only [Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
  · intro M
    exact ((jAdj B j').homEquiv _ _).apply_symm_apply _

/-- The module open compositor conjugate to the specified inverse-image compositor.
Source: Stacks, Tags 09AE and 0DV0
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleJComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    moduleJ B j ⋙ moduleJ B k ≅ moduleJ B (j ≫ k) :=
  Adjunction.leftAdjointCompIso (moduleJAdj B j) (moduleJAdj B k)
    (moduleJAdj B (j ≫ k)) (moduleGComp B j k).symm

/-- The inverse-image identity conjugate to the section-normalized direct-image identity.
Source: Stacks, Tag 07A7 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleGId (X : Scheme.{u}) : modulePullback B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Adjunction.leftAdjointIdIso (openBetaModuleAdj B (𝟙 X)) (moduleRId B X)

set_option backward.isDefEq.respectTransparency false

@[irreducible] private def moduleCompEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    modulePullback B h ≅ modulePullback B g ⋙ modulePullback B f :=
  eqToIso (congrArg (modulePullback B) w.symm) ≪≫ moduleGComp B f g

private theorem moduleCompEq_coherence {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    moduleCompEq B a bc abc hr ≪≫
        Functor.isoWhiskerRight (moduleCompEq B b c bc hbc) (modulePullback B a) =
      moduleCompEq B ab c abc hl ≪≫
        Functor.isoWhiskerLeft (modulePullback B c) (moduleCompEq B a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [moduleCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using ordinary_coherence a b c B M

private theorem moduleSquare_normalize {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) :
    moduleSquareG B k r p i w =
      (moduleCompEq B r i (k ≫ p) w.symm).symm ≪≫
        moduleCompEq B k p (k ≫ p) rfl := by
  rw [moduleSquareG_eq]
  unfold moduleCompEq
  exact normalizeIsoSquare (moduleGComp B r i) (moduleGComp B k p)
    (congrArg (modulePullback B) w.symm)

private theorem moduleCompEq_refl {V W S : Scheme.{u}} (f : V ⟶ W) (k : W ⟶ S) :
    moduleGComp B f k = moduleCompEq B f k (f ≫ k) rfl := by
  unfold moduleCompEq
  exact (Iso.refl_trans _).symm
private theorem moduleSquare_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Modules B X) :
    (moduleGComp B b a).hom.app ((modulePullback B j).obj N) ≫
        (modulePullback B b).map ((moduleSquareG B a j₁ j g w₁).inv.app N) ≫
        (moduleSquareG B b j₂ j₁ h w₂).inv.app ((modulePullback B g).obj N) =
      (moduleSquareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (modulePullback B j₂).map ((moduleGComp B h g).hom.app N) := by
  rw [moduleCompEq_refl B b a, moduleCompEq_refl B h g,
    moduleSquare_normalize B a j₁ j g w₁, moduleSquare_normalize B b j₂ j₁ h w₂,
    moduleSquare_normalize B (b ≫ a) j₂ j (h ≫ g) w]
  simp only [Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have first := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B b a j (b ≫ a) (a ≫ j) ((b ≫ a) ≫ j)
      rfl rfl rfl (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at first
  have first' := rearrange_square _ _ _ _ first.symm
  rw [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at first'
  rw [reassoc_of% first']
  have second := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B b j₁ g (b ≫ j₁) (a ≫ j) ((b ≫ a) ≫ j) rfl w₁.symm
      (by rw [Category.assoc, ← w₁, ← Category.assoc]) (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at second
  have second' := rearrange_square _ _ _ _ second
  simp only [NatIso.inv_hom_app] at second'
  rw [reassoc_of% second']
  rw [Iso.hom_inv_id_app_assoc]
  have key := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B j₂ h g (b ≫ j₁) (h ≫ g) ((b ≫ a) ≫ j)
      w₂.symm rfl (by rw [Category.assoc, ← w₁, ← Category.assoc]) w.symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [← key]

private theorem moduleSquare_flip {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG B r k i p h.symm = (moduleSquareG B k r p i h).symm := by
  simp only [moduleSquareG_eq, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem moduleInv_mate {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g) :
    mateEquiv (moduleJAdj B j) (moduleJAdj B j') (singleBetaInv B a j' j g w) =
      (moduleSquareG B a j' j g w).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  symm
  exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _

private theorem moduleJComp_conjugate {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    conjugateEquiv (moduleJAdj B (k ≫ j)) ((moduleJAdj B k).comp (moduleJAdj B j))
      (openBetaModuleJComp B k j).hom = (moduleGComp B k j).hom := by
  simp [openBetaModuleJComp, Adjunction.leftAdjointCompIso, conjugateIsoEquiv]

private theorem moduleInv_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (hp : ∀ N : Modules B X,
      (modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
        (moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
        (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N) =
      (moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (moduleGComp B k₁ j₁).hom.app ((modulePullback B g).obj N)) :
    singleBetaInv B b (k₁ ≫ j₁) (k ≫ j) g w =
      (((TwoSquare.mk _ _ _ _ (singleBetaInv B b k₁ k a wk)).vComp
        (TwoSquare.mk _ _ _ _ (singleBetaInv B a j₁ j g wj))).whiskerLeft
          (openBetaModuleJComp B k j).hom).whiskerRight (openBetaModuleJComp B k₁ j₁).inv := by
  apply (mateEquiv (moduleJAdj B (k ≫ j)) (moduleJAdj B (k₁ ≫ j₁))).injective
  rw [moduleInv_mate, mateEquiv_conjugateEquiv_vcomp _
    ((moduleJAdj B k₁).comp (moduleJAdj B j₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((moduleJAdj B k).comp (moduleJAdj B j)),
    mateEquiv_hcomp, moduleInv_mate, moduleInv_mate, moduleJComp_conjugate]
  rw [show conjugateEquiv ((moduleJAdj B k₁).comp (moduleJAdj B j₁)) (moduleJAdj B (k₁ ≫ j₁))
    (openBetaModuleJComp B k₁ j₁).inv = (moduleGComp B k₁ j₁).inv from
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _]
  refine NatTrans.ext (funext fun N ↦ ?_)
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp, TwoSquare.mk]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  set_option backward.isDefEq.respectTransparency false in
    change _ = ((modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
    ((moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
      (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N))) ≫
        (moduleGComp B k₁ j₁).inv.app ((modulePullback B g).obj N)
  rw [hp N]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- Open composition before evaluation.
Source: Stacks, Tags 04J0, 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: Restriction to successive opens is the same sectionwise restriction. Paste
these restriction comparisons and take successive open mates using the composite
open adjunction. The normalized open compositor is its conjugate. Invert the
resulting inverse-beta equation, the same equation remains valid on sheaves. -/
theorem openBetaModuleOpenComp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Modules B V) :
    (modulePullback B g).map ((openBetaModuleJComp B k j).inv.app M) ≫
        (openBetaModule B a j₁ j g wj sj).hom.app ((moduleJ B k).obj M) ≫
        (moduleJ B j₁).map ((openBetaModule B b k₁ k a wk sk).hom.app M) ≫
        (openBetaModuleJComp B k₁ j₁).hom.app ((modulePullback B b).obj M) =
      (openBetaModule B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  have hp (N : Modules B X) :
      (modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
        (moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
        (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N) =
      (moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (moduleGComp B k₁ j₁).hom.app ((modulePullback B g).obj N) := by
    have hh := moduleSquare_pasting_inv B g a b j k j₁ k₁
      wj.symm wk.symm w.symm N
    rw [moduleSquare_flip B a j₁ j g wj, moduleSquare_flip B b k₁ k a wk,
      moduleSquare_flip B b (k₁ ≫ j₁) (k ≫ j) g w] at hh
    simp only [Iso.symm_inv] at hh
    apply (cancel_epi ((moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).hom.app N)).1
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(modulePullback B k₁).map_id, Category.comp_id]
  have hi := congr_app (moduleInv_open_comp B k j k₁ j₁ a b g wk wj w hp) M
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk] at hi
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hi
  let e := openBetaModule B b (k₁ ≫ j₁) (k ≫ j) g w s
  let e₁ := openBetaModule B b k₁ k a wk sk
  let e₂ := openBetaModule B a j₁ j g wj sj
  change _ = e.hom.app M
  apply (cancel_epi (e.inv.app M)).1
  change (singleBetaInv B b (k₁ ≫ j₁) (k ≫ j) g w).app M ≫ _ = _
  rw [hi]
  simp only [Category.assoc]
  change (openBetaModuleJComp B k₁ j₁).inv.app _ ≫ (moduleJ B j₁).map (e₁.inv.app M) ≫
    e₂.inv.app ((moduleJ B k).obj M) ≫
      (modulePullback B g).map ((openBetaModuleJComp B k j).hom.app M) ≫
      (modulePullback B g).map ((openBetaModuleJComp B k j).inv.app M) ≫ e₂.hom.app _ ≫
        (moduleJ B j₁).map (e₁.hom.app M) ≫ (openBetaModuleJComp B k₁ j₁).hom.app _ = _
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app]
  erw [(modulePullback B g).map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(moduleJ B j₁).map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

section Finite

variable [Finite B] [TopologicalSpace B] [DiscreteTopology B]

section FiniteComparisonProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] C Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleRingModulePullback upperStar upperStarLowerStarAdjunction upperStarComp
  upperStarCompIso upperStarCongr

private lemma finiteMateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

private lemma finiteSquareTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {α : Sort*} (P : α → C ⥤ D) (Q : α → E ⥤ F)
    (R : E ⥤ C) (S : F ⥤ D) (q : ∀ x, TwoSquare R (Q x) (P x) S)
    {x y : α} (h : x = y)
    {P₁ P₂ : C ⥤ D} {Q₁ Q₂ : E ⥤ F}
    (a : P x ≅ P₁) (a' : P y ≅ P₂) (b : Q x ≅ Q₁) (b' : Q y ≅ Q₂)
    (p : TwoSquare R Q₁ P₁ S) (p' : TwoSquare R Q₂ P₂ S)
    (ha : p.whiskerRight a.hom = (q x).whiskerLeft b.hom)
    (ha' : p'.whiskerRight a'.hom = (q y).whiskerLeft b'.hom)
    (z : P₂ ≅ P₁) (w : Q₁ ≅ Q₂)
    (hz : z = a'.symm ≪≫ eqToIso (congrArg P h.symm) ≪≫ a)
    (hw : w = b.symm ≪≫ eqToIso (congrArg Q h) ≪≫ b') :
    p'.whiskerRight z.inv = p.whiskerLeft w.hom := by
  rw [hz, hw]
  subst y
  have h₁ (M : E) := congrArg (fun t ↦ t.app M) ha
  have h₂ (M : E) := congrArg (fun t ↦ t.app M) ha'
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁ h₂
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, eqToIso_refl,
    Iso.refl_trans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a.hom.app (R.obj M))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [h₂, reassoc_of% (h₁ M), ← S.map_comp_assoc, Iso.hom_inv_id_app,
    S.map_id, Category.id_comp]

private lemma finiteSquareComponents
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂) (R₃ : C₃ ⥤ D₃)
    (Qj : C₀ ⥤ C₁) (Qg : C₀ ⥤ C₂) (Qa : C₁ ⥤ C₃) (Qj' : C₂ ⥤ C₃)
    (Pj : D₀ ⥤ D₁) (Pg : D₀ ⥤ D₂) (Pa : D₁ ⥤ D₃) (Pj' : D₂ ⥤ D₃)
    (αj : R₀ ⋙ Pj ⟶ Qj ⋙ R₁) (αg : R₀ ⋙ Pg ⟶ Qg ⋙ R₂)
    (αa : R₁ ⋙ Pa ⟶ Qa ⋙ R₃) (αj' : R₂ ⋙ Pj' ⟶ Qj' ⋙ R₃)
    (z : Pg ⋙ Pj' ≅ Pj ⋙ Pa) (w : Qj ⋙ Qa ≅ Qg ⋙ Qj')
    (h : ((TwoSquare.mk _ _ _ _ αg).vComp (TwoSquare.mk _ _ _ _ αj')).whiskerRight
        z.inv =
      ((TwoSquare.mk _ _ _ _ αj).vComp (TwoSquare.mk _ _ _ _ αa)).whiskerLeft w.hom)
    (N : C₀) :
    z.inv.app (R₀.obj N) ≫ Pj'.map (αg.app N) ≫ αj'.app (Qg.obj N) =
      Pa.map (αj.app N) ≫ αa.app (Qj.obj N) ≫ R₃.map (w.hom.app N) := by
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
    using congrArg (fun t ↦ t.app N) h

private lemma finiteMateCube
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (sr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (bs : Mf ⋙ Hs ≅ Gs ⋙ Mf')
    (f : PY ⋙ Mf ≅ Lf ⋙ PX) (f' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (g : PY ⋙ Gs ≅ Gr ⋙ PY') (g' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (r : PX ⋙ Sf ≅ Rf ⋙ PY) (r' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (tr : Rf ⋙ Gr ⟶ Hr ⋙ Rf') (ts : Sf ⋙ Gs ⟶ Hs ⋙ Sf')
    (hf : mateEquiv af bf f.hom = TwoSquare.mk _ _ _ _ r.inv)
    (hf' : mateEquiv af' bf' f'.hom = TwoSquare.mk _ _ _ _ r'.inv)
    (hsr : mateEquiv af af' sr.hom = TwoSquare.mk _ _ _ _ tr)
    (hbs : mateEquiv bf bf' bs.inv = TwoSquare.mk _ _ _ _ ts)
    (h : ∀ K, ts.app (PX.obj K) ≫ Sf'.map (g'.hom.app K) ≫
      r'.hom.app (Hr.obj K) = Gs.map (r.hom.app K) ≫
        g.hom.app (Rf.obj K) ≫ PY'.map (tr.app K)) (M : DY) :
    bs.hom.app (PY.obj M) ≫ Mf'.map (g.hom.app M) ≫ f'.hom.app (Gr.obj M) =
      Hs.map (f.hom.app M) ≫ g'.hom.app (Lf.obj M) ≫ PX'.map (sr.inv.app M) := by
  have ht (K : DX) : g.hom.app (Rf.obj K) ≫ PY'.map (tr.app K) ≫
      r'.inv.app (Hr.obj K) = Gs.map (r.inv.app K) ≫
        ts.app (PX.obj K) ≫ Sf'.map (g'.hom.app K) := by
    apply (cancel_epi (Gs.map (r.hom.app K))).1
    simp only [← Gs.map_comp_assoc, Iso.hom_inv_id_app,
      Gs.map_id, Category.id_comp]
    apply (cancel_mono (r'.hom.app (Hr.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hh := (h K).symm
    dsimp only [Functor.comp_obj, Functor.comp_map] at hh ⊢
    simpa only [Category.comp_id] using hh
  have hc := mateEquiv_app_cube_converse af af' bf bf' sr.hom bs.inv
    f.hom f'.hom g.hom g'.hom (fun K ↦ by
      rw [hf, hf', hsr, hbs]
      exact ht K) M
  apply (cancel_epi (bs.inv.app (PY.obj M))).1
  apply (cancel_mono (PX'.map (sr.hom.app M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← PX'.map_comp,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.comp_map] at hc ⊢
  simpa only [PX'.map_id, Category.comp_id] using hc

end FiniteComparisonProof

end Finite

end AlgebraicGeometry.ProEtale.StrictTower

attribute [instance] CategoryTheory.catToReflQuiver
