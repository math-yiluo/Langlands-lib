/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumFlatKFlat
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomThickLocus

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
/-!
# Canonical étale open tensor and coefficient comparison data

Source: Stacks Tags 0GL1, 0E8I, 06YY, 03EL, 03DI and 0E8J
(blueprint: lem-coef-etale-open-comparison-data).

The ordinary comparisons are adjunction mates, not arbitrary isomorphisms. The
coefficient comparisons descend their degreewise maps on K-flat representatives.
All derived objects are in the ordinary unbounded constant-coefficient categories.

## Main definitions

* `canonicalGammaZero`, `canonicalGamma`: the ordinary and derived projection maps.
* `openScalarExtension`, `openScalarRestriction`: the fixed natural coefficient comparisons.
* `OpenScalarExtensionNormalization`, `OpenScalarRestrictionNormalization`: their K-flat models.

## Main statements

* `openScalarRestrictionMap_isIso`: invertibility of the fixed scalar/restriction mate.
* `OpenScalarExtensionNormalization`, `OpenScalarRestrictionNormalization`: fixed model laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Exact derived restriction. Source: Stacks 03DJ, 08FJ
(blueprint: lem-coef-etale-open-comparison-data). -/
abbrev derivedRestriction {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A U :=
  D((j)^*[ModuleCat.{u + 1} A])

/-- Exact derived extension by zero. Source: Stacks 03DJ, 08FJ
(blueprint: lem-coef-etale-open-comparison-data). -/
abbrev derivedExtension {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategoryModule A U ⥤ DerivedCategoryModule A X :=
  D((j)_!open[ModuleCat.{u + 1} A])

/-- The published canonical open projection map. Source: Stacks 0GL1
(blueprint: lem-coef-etale-open-comparison-data). -/
def canonicalGamma {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X) :=
  ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j).app P).app T

/-- Site flatness in the recorded constant-ring module coordinates. The realization
is the existing constant-module equivalence, not a newly chosen action.
Source: Stacks 03ER (blueprint: lem-coef-etale-open-comparison-data). -/
abbrev etaleFlat (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  SheafOfModules.IsFlatOnSite
    ((Scheme.etaleSumFlatModuleRealization T A).obj P)

/-- The recorded K-flat predicate after the same exact constant-module realization.
Source: Stacks 06YN (blueprint: lem-coef-etale-open-comparison-data). -/
abbrev etaleKFlat (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    ((Scheme.etaleSumFlatComplexRealization T A).obj P)

/-- Ordinary restriction commutes with restriction of coefficients. The middle
identification is literally the same sectionwise functor. Source: Stacks 03EL, 03EK
(blueprint: lem-coef-etale-open-comparison-data). -/
def openRestrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)^*[ModuleCat.{u + 1} B] ⋙ Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ (j)^*[ModuleCat.{u + 1} A] :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

/-- Canonical ordinary scalar/restriction comparison `r⁰`, the identification of
left adjoints to sectionwise direct image and restriction of scalars.
Source: Stacks 03EL, 03EK (blueprint: lem-coef-etale-open-comparison-data). -/
def openScalarRestrictionZero {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)^*[ModuleCat.{u + 1} A] ⋙ ProEtale.etaleSheafExtendScalars φ U ≅
      ProEtale.etaleSheafExtendScalars φ X ⋙ (j)^*[ModuleCat.{u + 1} B] :=
  (((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)).leftAdjointUniq
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ U)).ofNatIsoRight (Iso.refl _))).symm

/-- Canonical ordinary coefficient/open comparison `q⁰`: uniqueness of left
adjoints to the actual restriction/scalar functors fixes the isomorphism.
Source: Stacks 0E8I, 03DI (blueprint: lem-coef-etale-open-comparison-data). -/
def openScalarExtensionZero {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (j)_!open[ModuleCat.{u + 1} A] ⋙ ProEtale.etaleSheafExtendScalars φ X ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙ (j)_!open[ModuleCat.{u + 1} B] :=
  ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)).leftAdjointUniq
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (openRestrictScalarsIso φ j))

/-- Exact descent of the canonical restriction/scalar identification.
Source: Stacks 06YY, 08FJ (blueprint: lem-coef-etale-open-comparison-data). -/
def openDerivedRestrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := B) j ⋙ Sheaf.derivedRestrictScalars U.smallEtaleTopology φ ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ derivedRestriction (A := A) j :=
  Functor.mapDerivedCategorySquareIso (openRestrictScalarsIso φ j)

/-- Canonical derived `q`, using the degreewise derived open adjunction and the
published scalar adjunction. Source: Stacks 0E8I, 06YY, 08FJ
(blueprint: lem-coef-etale-open-comparison-data). -/
def openScalarExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)))
    (((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
        (openDerivedRestrictScalarsIso φ j))

/-- The canonical scalar/restriction mate, prior to asserting invertibility.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-comparison-data). -/
def openScalarRestrictionMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := A) j ⋙ scalarExtension φ U ⟶
      scalarExtension φ X ⋙ derivedRestriction (A := B) j :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))).symm
      (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv))

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem leftUniq_whiskerLeft
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {F G : D ⥤ E} {S : E ⥤ D} (b : F ⊣ S) (c : G ⊣ S) :
    ((a.comp b).leftAdjointUniq (a.comp c)).hom =
      Functor.whiskerLeft L (b.leftAdjointUniq c).hom := by
  apply (conjugateEquiv (a.comp c) (a.comp b)).injective
  rw [conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]

private theorem leftUniq_whiskerRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {S : D ⥤ C} (b : F ⊣ S) (c : G ⊣ S)
    {L : D ⥤ E} {R : E ⥤ D} (a : L ⊣ R) :
    ((b.comp a).leftAdjointUniq (c.comp a)).hom =
      Functor.whiskerRight (b.leftAdjointUniq c).hom L := by
  apply (conjugateEquiv (c.comp a) (b.comp a)).injective
  rw [conjugateEquiv_whiskerRight]
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv]

private theorem openRestrictScalarsIso_inv_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openRestrictScalarsIso φ j).inv = (upperStarRestrictScalarsIsoSheaf φ j).hom := by
  let a := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let d := Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ
  let b' := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let c' := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j
  have hadj : a.comp b' = c'.comp d := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change ((a.comp b').unit.app M).hom.app V = ((c'.comp d).unit.app M).hom.app V
    simp only [Adjunction.comp_unit_app]
    dsimp only [a, b', c', d]
    let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
      (inferInstance : Etale j) trivial
    let t := M.obj.map (siteAdj.counit.app V.unop).op
    change ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app M).hom.app V ≫
        (ModuleCat.coextendScalars φ).map ((ModuleCat.restrictScalars φ).map t) =
      t ≫ ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ).unit.app
        ((openImmersionRestriction (ModuleCat B) j).obj M)).hom.app _
    rw [restrictCoextendScalarsAdj_unit_app_hom_app,
      restrictCoextendScalarsAdj_unit_app_hom_app]
    exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.naturality t).symm
  change _ = ((a.comp b).leftAdjointUniq (c.comp d)).hom
  calc
    (openRestrictScalarsIso φ j).inv =
        ((a.comp b).leftAdjointUniq (a.comp b')).hom ≫
          ((c'.comp d).leftAdjointUniq (c.comp d)).hom := by
      have hleft := leftUniq_whiskerLeft a b b'
      have hright := leftUniq_whiskerRight c' c d
      have hcomp := congrArg₂ (fun f g ↦ f ≫ g) hleft hright
      refine Eq.trans ?_ hcomp.symm
      ext M
      simp only [openRestrictScalarsIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, upperStarIsoOpenImmersionRestriction]
      rfl
    _ = _ := by
      rw [← hadj, Adjunction.leftAdjointUniq_trans]

private theorem inverse_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ U) (b : M ⊣ V)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (x : TwoSquare U H G V) (e : G ≅ G') (f : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk U H' G' V
        (Functor.whiskerLeft U e.inv ≫ x ≫ Functor.whiskerRight f.hom V))) =
      Functor.whiskerRight e.inv M ≫ ((mateEquiv a b).symm x) ≫
        Functor.whiskerLeft L f.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  have he := e.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at he
  rw [← M.map_comp_assoc, he, M.map_comp]
  simp only [Category.assoc]
  have hf := b.counit.naturality (f.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hf]

private theorem derived_square_symm
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j) :
    (Functor.mapDerivedCategorySquareIso (openRestrictScalarsIso φ j)).inv =
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom := by
  rw [← he]
  ext K
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rfl

private theorem exact_scalar_mate_etale
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q))).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIsoSheaf q f)).hom)) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso q f).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} S) f
  have hx : IsIso ((mateEquiv a b).symm x) := (ProEtale.scalarPullbackReverse_isIso q f).2
  have h := inverse_mate_transport a b x e e'
  have ht : IsIso (Functor.whiskerRight e.inv _ ≫
      ((mateEquiv a b).symm x) ≫ Functor.whiskerLeft _ e'.hom) := inferInstance
  rw [← h] at ht
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf q f)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
          e.inv ≫ x ≫
          Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)) := by
    ext M
    dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [← heq] at ht
  exact ht

/-- The canonical mate is invertible for arbitrary coefficient maps.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-comparison-data).
Proof: ordinary restriction is restriction along the slice-site localization.
Its sectionwise coefficient square is the identity. The two composite adjunctions
with coextension of scalars have the same unit by naturality of the coefficient
unit. Uniqueness of left adjoints therefore identifies that square with the
published scalar/pullback square. Exact descent preserves its inverse. Transport
the published invertible scalar inverse mate along the exact/left-derived
restriction isomorphisms; the mate transport identity identifies the result
with precisely the map in the statement. -/
@[instance] theorem openScalarRestrictionMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openScalarRestrictionMap φ j) := by
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have hd := derived_square_symm φ j he
  dsimp only [openScalarRestrictionMap, openDerivedRestrictScalarsIso]
  rw [hd]
  exact exact_scalar_mate_etale φ j

/-- The canonical natural isomorphism `r`, with its hom fixed as the specified mate.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-comparison-data). -/
def openScalarRestriction {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j :=
  asIso (openScalarRestrictionMap φ j)

/-- The ordinary projection map `γ⁰`, defined as the open-adjunction adjunct
of the unit followed by the canonical restriction/tensor comparison.
Source: Stacks 0E8I, 03EL (blueprint: lem-coef-etale-open-comparison-data). -/
def canonicalGammaZero
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : Sheaf U.smallEtaleTopology C) (T : Sheaf X.smallEtaleTopology C) :
    (j)_!open[C].obj (P ⊗ (j)^*[C].obj T) ⟶ (j)_!open[C].obj P ⊗ T :=
  ((openImmersionLowerShriekUpperStarAdjunction C j).homEquiv _ _).symm
    ((tensorRightUpperStarIso C j T).hom.app P)

/-- K-flat model normalization of `q`, expressed by the published scalar derived
counits and the exact open localization factors. The bottom chain map is the
ordinary canonical `q⁰` applied degreewise.
Source: Stacks 0E8I, 06YY (blueprint: lem-coef-etale-open-comparison-data). -/
def OpenScalarExtensionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (q : derivedExtension (A := A) j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ derivedExtension (A := B) j) : Prop :=
  ∀ P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat U A P →
    q.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        (derivedExtension (A := B) j).map (scalarExtensionRepresentative φ U P) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ U).mapHomologicalComplex (.up ℤ)).obj P) =
      (scalarExtension φ X).map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionRepresentative φ X
          (((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ j) (.up ℤ)).hom.app P)

/-- K-flat model normalization of `r`. The bottom map is the canonical ordinary
restriction/balancing map `r⁰`, applied degreewise, not a free iso parameter.
Source: Stacks 03EL, 06YY (blueprint: lem-coef-etale-open-comparison-data). -/
def OpenScalarRestrictionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : derivedRestriction (A := A) j ⋙ scalarExtension φ U ≅
      scalarExtension φ X ⋙ derivedRestriction (A := B) j) : Prop :=
  ∀ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
    etaleKFlat X A P →
    r.hom.app (_root_.DerivedCategory.Q.obj P) ≫
        (derivedRestriction (A := B) j).map (scalarExtensionRepresentative φ X P) ≫
        (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategoryFactors.hom.app
          (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) =
      (scalarExtension φ U).map
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionRepresentative φ U
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (openScalarRestrictionZero φ j) (.up ℤ)).hom.app P)

section ExactTensor

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction/tensor comparison with exact restriction in both arguments.
Its tensorator is the published K-flat pullback tensor comparison, transported
by the published exact/left-derived restriction identification.
Source: Stacks 03EL, 0GL1 (blueprint: lem-coef-etale-open-comparison-data). -/
def openExactRestrictionTensor
    (T₁ T₂ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((derivedTensor C U).obj (D((j)^*[C]).obj T₁)).obj (D((j)^*[C]).obj T₂) ≅
      D((j)^*[C]).obj (((derivedTensor C X).obj T₁).obj T₂) :=
  ((derivedTensor C U).obj (D((j)^*[C]).obj T₁)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory C j).app T₂).symm ≪≫
    ((mapDerivedCategoryUpperStarDerivedTensorIso C j).app T₁).app T₂

/-- The canonical projection map written with exact `j^*`. The change from
`Lj^*` is the existing exact/left-derived comparison, not a new derived functor.
Source: Stacks 0GL1 (blueprint: lem-coef-etale-open-comparison-data). -/
def canonicalGammaExact
    (P : _root_.DerivedCategory (Sheaf U.smallEtaleTopology C))
    (T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    D((j)_!open[C]).obj (((derivedTensor C U).obj P).obj (D((j)^*[C]).obj T)) ⟶
      ((derivedTensor C X).obj (D((j)_!open[C]).obj P)).obj T :=
  D((j)_!open[C]).map
      (((derivedTensor C U).obj P).map
        ((leftDerivedUpperStarIsoMapDerivedCategory C j).inv.app T)) ≫
    ((derivedOpenImmersionLowerShriekProjectionMap C j).app P).app T

end ExactTensor

end AlgebraicGeometry.Etale
