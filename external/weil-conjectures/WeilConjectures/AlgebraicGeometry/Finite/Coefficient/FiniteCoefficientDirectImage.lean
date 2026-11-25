/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantProjectionFormula
import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing

import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude

/-!
# Finite coefficient change for ordinary direct image

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
node order 2130 (blueprint: lemma-change-coefficients-direct-image--1).

Scalar extension is the published left adjoint to exact derived restriction.
The coefficient map is uniquely fixed by its scalar-unit/counit equation in D(B).
The equation is the scalar-adjunction form of extending the A-coefficient counit.
It does not use faithfulness of derived scalar restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Fix the pro-etale site-size universe before elaborating scalar functors.

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance
private theorem cachedEtaleMonoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleCoproducts (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasCountableCoproducts (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleFlatResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasFunctorialFlatResolution (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleInjectiveResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasKInjectiveResolutions (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleExactColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleTensor4 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedEtaleTensor12 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensor23 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensorColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).obj V) :=
  inferInstance
private theorem cachedEtaleTensorFlipColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj V) :=
  inferInstance

private theorem reverse_mate_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {S₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (adj₀ : S₀ ⊣ R₀)
    {S₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (adj₁ : S₁ ⊣ R₁)
    {S₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (adj₂ : S₂ ⊣ R₂)
    {Lf : A₀ ⥤ A₁} {Lg : A₁ ⥤ A₂} {Lh : A₀ ⥤ A₂}
    {Lf' : B₀ ⥤ B₁} {Lg' : B₁ ⥤ B₂} {Lh' : B₀ ⥤ B₂}
    (ef : R₀ ⋙ Lf ≅ Lf' ⋙ R₁) (eg : R₁ ⋙ Lg ≅ Lg' ⋙ R₂)
    (eh : R₀ ⋙ Lh ≅ Lh' ⋙ R₂) (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
    (hc : ∀ M : B₀, eh.hom.app M ≫ R₂.map (e'.hom.app M) =
      e.hom.app (R₀.obj M) ≫ Lg.map (ef.hom.app M) ≫ eg.hom.app (Lf'.obj M)) :
    Adjunction.ExchangeCompCompatible
      (((mateEquiv adj₀ adj₁).symm (TwoSquare.mk _ _ _ _ ef.hom)))
      (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ eg.hom)))
      (((mateEquiv adj₀ adj₂).symm (TwoSquare.mk _ _ _ _ eh.hom))) e e' := by
  let kf := ((mateEquiv adj₀ adj₁).symm (TwoSquare.mk _ _ _ _ ef.hom))
  let kg := ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ eg.hom))
  let kh := ((mateEquiv adj₀ adj₂).symm (TwoSquare.mk _ _ _ _ eh.hom))
  have hf (M : A₀) : Lf.map (adj₀.unit.app M) ≫ ef.hom.app (S₀.obj M) =
      adj₁.unit.app (Lf.obj M) ≫ R₁.map (kf.app M) :=
    unit_mateEquiv_symm adj₀ adj₁ (TwoSquare.mk _ _ _ _ ef.hom) M
  have hg (M : A₁) : Lg.map (adj₁.unit.app M) ≫ eg.hom.app (S₁.obj M) =
      adj₂.unit.app (Lg.obj M) ≫ R₂.map (kg.app M) :=
    unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ eg.hom) M
  have hh (M : A₀) : Lh.map (adj₀.unit.app M) ≫ eh.hom.app (S₀.obj M) =
      adj₂.unit.app (Lh.obj M) ≫ R₂.map (kh.app M) :=
    unit_mateEquiv_symm adj₀ adj₂ (TwoSquare.mk _ _ _ _ eh.hom) M
  constructor
  intro M
  change S₂.map (e.hom.app M) ≫ kg.app (Lf.obj M) ≫ Lg'.map (kf.app M) =
    kh.app M ≫ e'.hom.app (S₀.obj M)
  apply (adj₂.homEquiv _ _).injective
  change adj₂.unit.app _ ≫ R₂.map _ = adj₂.unit.app _ ≫ R₂.map _
  simp only [Functor.map_comp]
  erw [← adj₂.unit.naturality_assoc]
  simp only [Functor.id_map, Functor.comp_obj]
  rw [← reassoc_of% (hg (Lf.obj M))]
  erw [← eg.hom.naturality]
  simp only [Functor.comp_map]
  slice_lhs 2 3 => rw [← Lg.map_comp, ← hf, Lg.map_comp]
  slice_lhs 1 2 => exact (e.hom.naturality (adj₀.unit.app M)).symm
  simp only [Category.assoc, Functor.comp_obj]
  rw [← hc, ← Category.assoc, hh]
  simp only [Category.assoc]

private theorem rightAdjointUniq_ofNatIsoLeft_hom
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ L') :
    (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj').hom =
      conjugateEquiv adj adj' e.inv := by
  ext X
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.map_comp, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app]
  erw [R'.map_id, Category.id_comp]

private theorem coefficient_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom)))) (K : A) :
    ∃! c : S.obj (P.obj K) ⟶ P'.obj (S'.obj K),
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map c ≫ adjB.counit.app (S'.obj K)) =
          adjA.counit.app K ≫ adjT.unit.app K := by
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom))
  have : IsIso k := hk
  let t := inv (k.app (P.obj K)) ≫ S'.map (adjA.counit.app K)
  let c := adjB.homEquiv _ _ t
  have hunit := unit_mateEquiv_symm adjX adjT (TwoSquare.mk _ _ _ _ e.hom) (P.obj K)
  have hc : Q'.map c ≫ adjB.counit.app (S'.obj K) = t := by
    exact (adjB.homEquiv _ _).symm_apply_apply t
  have eqn (d : S.obj (P.obj K) ⟶ P'.obj (S'.obj K)) :
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map d ≫ adjB.counit.app (S'.obj K)) =
      adjT.homEquiv _ _ (k.app (P.obj K) ≫
        (Q'.map d ≫ adjB.counit.app (S'.obj K))) := by
    rw [Adjunction.homEquiv_unit]
    rw [← Category.assoc, hunit]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  refine ⟨c, ?_, ?_⟩
  · dsimp only
    rw [eqn, hc]
    dsimp only [t]
    rw [IsIso.hom_inv_id_assoc, Adjunction.homEquiv_unit]
    exact adjT.unit.naturality (adjA.counit.app K) |>.symm
  · intro d hd
    rw [eqn] at hd
    have hc' : adjT.homEquiv _ _ (k.app (P.obj K) ≫
        (Q'.map c ≫ adjB.counit.app (S'.obj K))) =
        adjA.counit.app K ≫ adjT.unit.app K := by
      rw [hc]
      dsimp only [t]
      rw [IsIso.hom_inv_id_assoc, Adjunction.homEquiv_unit]
      exact adjT.unit.naturality (adjA.counit.app K) |>.symm
    apply (adjB.homEquiv _ _).symm.injective
    apply (cancel_epi (k.app (P.obj K))).mp
    exact (adjT.homEquiv _ _).injective (hd.trans hc'.symm)

private theorem coefficient_eq_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom))))
    (K : A) (c : S.obj (P.obj K) ⟶ P'.obj (S'.obj K))
    (hu : ∀ d, Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
      R'.map (Q'.map d ≫ adjB.counit.app (S'.obj K)) =
        adjA.counit.app K ≫ adjT.unit.app K → d = c) :
    c = (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _
      (@asIso _ _ _ _ _ hk).inv)).app K := by
  symm
  apply hu
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom))
  have hunit := unit_mateEquiv_symm adjX adjT
    (TwoSquare.mk _ _ _ _ e.hom) (P.obj K)
  change Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) =
    adjT.unit.app (Q.obj (P.obj K)) ≫ R'.map (k.app (P.obj K)) at hunit
  have hc := mateEquiv_counit adjA adjB
    (TwoSquare.mk _ _ _ _ (@asIso _ _ _ _ _ hk).inv) K
  rw [hc, ← Category.assoc, hunit, Category.assoc, ← R'.map_comp]
  change adjT.unit.app _ ≫
    R'.map ((@asIso _ _ _ _ _ hk).hom.app _ ≫
      (@asIso _ _ _ _ _ hk).inv.app _ ≫ _) = _
  rw [Iso.hom_inv_id_app_assoc]
  exact (adjT.unit.naturality (adjA.counit.app K)).symm

private theorem coefficient_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom))))
    (c : ∀ K, S.obj (P.obj K) ⟶ P'.obj (S'.obj K))
    (hu : ∀ K (d : S.obj (P.obj K) ⟶ P'.obj (S'.obj K)),
      Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
        R'.map (Q'.map d ≫ adjB.counit.app (S'.obj K)) =
          adjA.counit.app K ≫ adjT.unit.app K → d = c K)
    {K L : A} (h : K ⟶ L) :
    S.map (P.map h) ≫ c L = c K ≫ P'.map (S'.map h) := by
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom))
  have : IsIso k := hk
  let γ := (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv))
  have heq (M : A) : γ.app M = c M := by
    apply hu M
    have hunit := unit_mateEquiv_symm adjX adjT
      (TwoSquare.mk _ _ _ _ e.hom) (P.obj M)
    change Q.map (adjX.unit.app (P.obj M)) ≫ e.hom.app (S.obj (P.obj M)) =
      adjT.unit.app (Q.obj (P.obj M)) ≫ R'.map (k.app (P.obj M)) at hunit
    have hc := mateEquiv_counit adjA adjB (TwoSquare.mk _ _ _ _ (asIso k).inv) M
    change Q'.map (γ.app M) ≫ adjB.counit.app (S'.obj M) =
      (asIso k).inv.app (P.obj M) ≫ S'.map (adjA.counit.app M) at hc
    rw [hc, ← Category.assoc, hunit, Category.assoc, ← R'.map_comp]
    change adjT.unit.app _ ≫
      R'.map ((asIso k).hom.app _ ≫ (asIso k).inv.app _ ≫ _) = _
    rw [Iso.hom_inv_id_app_assoc]
    exact (adjT.unit.naturality (adjA.counit.app M)).symm
  simpa only [Functor.comp_map, heq] using γ.naturality h

/-- Explicit size witness for the small etale site; no universe equality is imposed.
Source: Mathlib essentiallySmall_of_small_of_locallySmall; blueprint order 2130
(blueprint: lemma-change-coefficients-direct-image--1). -/
instance AlgebraicGeometry.Etale.finiteCoefficientSiteSize (X : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

namespace AlgebraicGeometry.Etale

/-- Canonical exact restriction/pullback comparison, in the unbounded categories.
Source: blueprint order 2130; Stacks Tags 07A4 and 07A6
(blueprint: lemma-change-coefficients-direct-image--1). -/
def finiteCoefficientRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _

/-- The equation fixing the coefficient projection map. Precomposing its B-counit
transpose with the pulled-back scalar unit gives the A-counit followed by the input
scalar unit. This is precisely extension of the counit after pullback/scalar
extension, expressed without choosing flat resolutions or an arbitrary comparison.
Source: blueprint order 2130, statement and proof Step 3; Stacks Tag 07A6
(blueprint: lemma-change-coefficients-direct-image--1). -/
def IsFiniteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A)))
    (c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K)) :
    Prop :=
  L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ)).unit.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (finiteCoefficientRestrictionPullback φ f).hom.app
      ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ).map
      (L(upperStar (ModuleCat.{u + 1} B) f).map c ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K)) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ)).unit.app K

/-- Existence and uniqueness of the specified coefficient map, without finiteness or
flatness of the coefficient morphism. These are properties of its construction.
Source: blueprint order 2130, coefficient-map definition and proof Steps 2--3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: use lem-pur-derived-change-of-rings to compute scalar extension on flat K-flat
representatives. Inverse image commutes with it by the canonical balancing comparison
of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Transpose scalar extension of the
A-counit through the B inverse-image/direct-image adjunction. The scalar adjunction
unit identity gives the displayed equation. Conversely that equation determines the
B-transpose by universality of the pulled-back scalar unit, then determines the map
by injectivity of the B geometric adjunction. No isomorphism assertion is used here. -/
theorem finiteCoefficientDirectImageMap_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    ∃! c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K),
      IsFiniteCoefficientDirectImageMap φ f K c := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  exact coefficient_existsUnique _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2 K

/-- The actual B-linear coefficient projection map, chosen from a theorem that
uniquely determines it by the extended counit. Only that proof is postponed.
Source: blueprint order 2130 (blueprint: lemma-change-coefficients-direct-image--1). -/
def finiteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K) :=
  (finiteCoefficientDirectImageMap_existsUnique φ f K).choose

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The equation fixing the coefficient projection map. Precomposing its B-counit
transpose with the pulled-back scalar unit gives the A-counit followed by the input
scalar unit. This is precisely extension of the counit after pullback/scalar
extension, expressed without choosing flat resolutions or an arbitrary comparison.
Source: blueprint order 2130, statement and proof Step 3; Stacks Tag 07A6
(blueprint: lemma-change-coefficients-direct-image--1). -/
def IsFiniteCoefficientDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K)) :
    Prop :=
  L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).unit.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
      ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
      (L(upperStar (ModuleCat.{u + 1} B) f).map c ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K))
            =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ)).unit.app K

/-- Existence and uniqueness of the specified coefficient map, without finiteness or
flatness of the coefficient morphism. These are properties of its construction.
Source: blueprint order 2130, coefficient-map definition and proof Steps 2--3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: use lem-pur-derived-change-of-rings to compute scalar extension on flat K-flat
representatives. Inverse image commutes with it by the canonical balancing comparison
of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Transpose scalar extension of the
A-counit through the B inverse-image/direct-image adjunction. The scalar adjunction
unit identity gives the displayed equation. Conversely that equation determines the
B-transpose by universality of the pulled-back scalar unit, then determines the map
by injectivity of the B geometric adjunction. No isomorphism assertion is used here. -/
theorem finiteCoefficientDirectImageMap_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ∃! c : (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K),
      IsFiniteCoefficientDirectImageMap φ f K c := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let aa := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f
  let ab := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let e := leftDerivedUpperStarRestrictScalarsIso.{u} φ f
  have hk := (scalarPullbackReverse_isIso.{u} φ f).1
  exact @coefficient_existsUnique.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    inferInstance inferInstance inferInstance inferInstance
    (R(lowerStar (ModuleCat.{u + 1} A) f)) (L(upperStar (ModuleCat.{u + 1} A) f)) aa
    (R(lowerStar (ModuleCat.{u + 1} B) f)) (L(upperStar (ModuleCat.{u + 1} B) f)) ab
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ) ax
    (pbcFixedScalarExtension (Scheme.ProEt.topology T) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ) adt e hk K

/-- The actual B-linear coefficient projection map, chosen from a theorem that
uniquely determines it by the extended counit. Only that proof is postponed.
Source: blueprint order 2130 (blueprint: lemma-change-coefficients-direct-image--1). -/
def finiteCoefficientChangeDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
        ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K) :=
  (finiteCoefficientDirectImageMap_existsUnique φ f K).choose

end AlgebraicGeometry.ProEtale

section CoefficientChainHelpers
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStar
attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

private theorem unit_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {S : A ⥤ B} {R : B ⥤ A} (a : S ⊣ R)
    {T : B ⥤ C} {U : C ⥤ B} (b : T ⊣ U)
    {V : A ⥤ C} {W : C ⥤ A} (c : V ⊣ W) (e : U ⋙ R ≅ W) (M : A) :
    c.unit.app M ≫ W.map ((Adjunction.leftAdjointCompIso a b c e).inv.app M) =
      a.unit.app M ≫ R.map (b.unit.app (S.obj M)) ≫ e.hom.app ((S ⋙ T).obj M) := by
  have h := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c e).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at h
  simpa only [Adjunction.comp_unit_app, Category.assoc] using h.symm
private theorem unit_comp_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    {S : A ⥤ B} {R : B ⥤ A} (a : S ⊣ R)
    {T : B ⥤ C} {U : C ⥤ B} (b : T ⊣ U)
    {V : A ⥤ C} {W : C ⥤ A} (c : V ⊣ W) (e : U ⋙ R ≅ W) (M : A) :
    c.unit.app M ≫ e.inv.app (V.obj M) =
      a.unit.app M ≫ R.map (b.unit.app (S.obj M)) ≫
        (U ⋙ R).map ((Adjunction.leftAdjointCompIso a b c e).hom.app M) := by
  have h := unit_conjugateEquiv c (a.comp b)
    (Adjunction.leftAdjointCompIso a b c e).hom M
  have hc : conjugateEquiv c (a.comp b)
      (Adjunction.leftAdjointCompIso a b c e).hom = e.inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply e.symm)
  rw [hc] at h
  simpa only [Adjunction.comp_unit_app, Category.assoc] using h

private theorem reverse_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {S₀₁ : A₀ ⥤ A₁} {R₁₀ : A₁ ⥤ A₀} (a₀₁ : S₀₁ ⊣ R₁₀)
    {S₁₂ : A₁ ⥤ A₂} {R₂₁ : A₂ ⥤ A₁} (a₁₂ : S₁₂ ⊣ R₂₁)
    {S₀₂ : A₀ ⥤ A₂} {R₂₀ : A₂ ⥤ A₀} (a₀₂ : S₀₂ ⊣ R₂₀)
    {T₀₁ : B₀ ⥤ B₁} {U₁₀ : B₁ ⥤ B₀} (b₀₁ : T₀₁ ⊣ U₁₀)
    {T₁₂ : B₁ ⥤ B₂} {U₂₁ : B₂ ⥤ B₁} (b₁₂ : T₁₂ ⊣ U₂₁)
    {T₀₂ : B₀ ⥤ B₂} {U₂₀ : B₂ ⥤ B₀} (b₀₂ : T₀₂ ⊣ U₂₀)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    (e₀₁ : R₁₀ ⋙ Q₀ ⟶ Q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ Q₁ ⟶ Q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ Q₀ ⟶ Q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.app M = Q₀.map (r.inv.app M) ≫
      e₀₁.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.app M) ≫ t.hom.app (Q₂.obj M))
    (M : A₀) :
    ((mateEquiv a₀₂ b₀₂).symm (TwoSquare.mk _ _ _ _ e₀₂)).app M =
      (Adjunction.leftAdjointCompIso b₀₁ b₁₂ b₀₂ t).inv.app (Q₀.obj M) ≫
      T₁₂.map (((mateEquiv a₀₁ b₀₁).symm (TwoSquare.mk _ _ _ _ e₀₁)).app M) ≫
      ((mateEquiv a₁₂ b₁₂).symm (TwoSquare.mk _ _ _ _ e₁₂)).app (S₀₁.obj M) ≫
      Q₂.map ((Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ r).hom.app M) := by
  let k₀₁ := ((mateEquiv a₀₁ b₀₁).symm (TwoSquare.mk _ _ _ _ e₀₁))
  let k₁₂ := ((mateEquiv a₁₂ b₁₂).symm (TwoSquare.mk _ _ _ _ e₁₂))
  apply (b₀₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu : Q₀.map (a₀₂.unit.app M) ≫ e₀₂.app (S₀₂.obj M) =
      b₀₂.unit.app (Q₀.obj M) ≫ U₂₀.map
        (((mateEquiv a₀₂ b₀₂).symm (TwoSquare.mk _ _ _ _ e₀₂)).app M) :=
    unit_mateEquiv_symm a₀₂ b₀₂ (TwoSquare.mk _ _ _ _ e₀₂) M
  rw [← hu, he]
  slice_lhs 1 2 => rw [← Q₀.map_comp, unit_comp_hom a₀₁ a₁₂ a₀₂ r M, Q₀.map_comp, Q₀.map_comp]
  slice_rhs 1 2 => rw [unit_comp b₀₁ b₁₂ b₀₂ t (Q₀.obj M)]
  simp only [Category.assoc]
  erw [← t.hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← t.hom.naturality_assoc, ← t.hom.naturality]
  simp only [Functor.comp_map]
  have hu₀₁ : Q₀.map (a₀₁.unit.app M) ≫ e₀₁.app (S₀₁.obj M) =
      b₀₁.unit.app (Q₀.obj M) ≫ U₁₀.map (k₀₁.app M) :=
    unit_mateEquiv_symm a₀₁ b₀₁ (TwoSquare.mk _ _ _ _ e₀₁) M
  have hu₁₂ : Q₁.map (a₁₂.unit.app (S₀₁.obj M)) ≫
      e₁₂.app (S₁₂.obj (S₀₁.obj M)) =
      b₁₂.unit.app (Q₁.obj (S₀₁.obj M)) ≫ U₂₁.map (k₁₂.app (S₀₁.obj M)) :=
    unit_mateEquiv_symm a₁₂ b₁₂ (TwoSquare.mk _ _ _ _ e₁₂) (S₀₁.obj M)
  change _ = b₀₁.unit.app _ ≫ U₁₀.map (b₁₂.unit.app _) ≫
    U₁₀.map (U₂₁.map (T₁₂.map (k₀₁.app M))) ≫ U₁₀.map (U₂₁.map
      (k₁₂.app (S₀₁.obj M))) ≫ U₁₀.map (U₂₁.map (Q₂.map _)) ≫ _
  slice_rhs 2 3 =>
    rw [← U₁₀.map_comp]
    erw [← b₁₂.unit.naturality]
    rw [U₁₀.map_comp]
  simp only [Functor.id_map, Functor.comp_obj]
  slice_rhs 1 2 => rw [← hu₀₁]
  simp only [Category.assoc]
  slice_rhs 3 4 => rw [← U₁₀.map_comp, ← hu₁₂, U₁₀.map_comp]
  simp only [Category.assoc]
  slice_rhs 4 5 =>
    rw [← U₁₀.map_comp]
    erw [← e₁₂.naturality]
    rw [U₁₀.map_comp]
  simp only [Category.assoc]
  erw [← e₀₁.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← e₀₁.naturality_assoc]
  rfl

private theorem mate_chain
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {Q : B ⥤ A} (adj : Q ⊣ P)
    {P' : C ⥤ D} {Q' : D ⥤ C} (adj' : Q' ⊣ P')
    {P'' : E ⥤ F} {Q'' : F ⥤ E} (adj'' : Q'' ⊣ P'')
    {S : B ⥤ D} {S' : A ⥤ C} {T : D ⥤ F} {T' : C ⥤ E}
    {U : B ⥤ F} {U' : A ⥤ E}
    (α : S ⋙ Q' ⟶ Q ⋙ S') (β : T ⋙ Q'' ⟶ Q' ⋙ T')
    (γ : U ⋙ Q'' ⟶ Q ⋙ U') (c : S ⋙ T ≅ U) (c' : S' ⋙ T' ≅ U')
    (hγ : ∀ M : B, γ.app M = Q''.map (c.inv.app M) ≫ β.app (S.obj M) ≫
      T'.map (α.app M) ≫ c'.hom.app (Q.obj M)) (K : A) :
    (mateEquiv adj adj'' (TwoSquare.mk _ _ _ _ γ)).app K =
      c.inv.app (P.obj K) ≫ T.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α)).app K) ≫
        (mateEquiv adj' adj'' (TwoSquare.mk _ _ _ _ β)).app (S'.obj K) ≫
        P''.map (c'.hom.app K) := by
  apply Adjunction.ext_of_comp_counit (adj := adj'')
  simp only [Functor.map_comp, Category.assoc]
  erw [adj''.counit_naturality]
  rw [mateEquiv_counit]
  rw [reassoc_of% (mateEquiv_counit adj' adj'' (TwoSquare.mk _ _ _ _ β) (S'.obj K)), hγ]
  simp only [Category.assoc]
  dsimp only [TwoSquare.mk]
  erw [β.naturality_assoc]
  simp only [Functor.comp_map]
  slice_rhs 3 4 => rw [← T'.map_comp, mateEquiv_counit, T'.map_comp]
  simp only [Category.assoc]
  rw [← c'.hom.naturality]
  rfl

private theorem derive_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (v + 1)}
    [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
    [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{v} A₀] [HasDerivedCategory.{v} A₁] [HasDerivedCategory.{v} A₂]
    [HasDerivedCategory.{v} B₀] [HasDerivedCategory.{v} B₁] [HasDerivedCategory.{v} B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    [R₁₀.Additive] [R₂₁.Additive] [R₂₀.Additive]
    [U₁₀.Additive] [U₂₁.Additive] [U₂₀.Additive]
    [Q₀.Additive] [Q₁.Additive] [Q₂.Additive]
    [PreservesFiniteLimits R₁₀] [PreservesFiniteColimits R₁₀]
    [PreservesFiniteLimits R₂₁] [PreservesFiniteColimits R₂₁]
    [PreservesFiniteLimits R₂₀] [PreservesFiniteColimits R₂₀]
    [PreservesFiniteLimits U₁₀] [PreservesFiniteColimits U₁₀]
    [PreservesFiniteLimits U₂₁] [PreservesFiniteColimits U₂₁]
    [PreservesFiniteLimits U₂₀] [PreservesFiniteColimits U₂₀]
    [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
    [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
    [PreservesFiniteLimits Q₂] [PreservesFiniteColimits Q₂]
    (e₀₁ : R₁₀ ⋙ Q₀ ≅ Q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ Q₁ ≅ Q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ Q₀ ≅ Q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = Q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (Q₂.obj M))
    (M : DerivedCategory A₂) :
    (Functor.mapDerivedCategorySquareIso e₀₂).hom.app M =
      Q₀.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso R₂₁ R₁₀ ≪≫
          Functor.mapDerivedCategoryNatIso r).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso e₀₁).hom.app (R₂₁.mapDerivedCategory.obj M) ≫
      U₁₀.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso e₁₂).hom.app M) ≫
      (Functor.mapDerivedCategoryCompIso U₂₁ U₁₀ ≪≫
        Functor.mapDerivedCategoryNatIso t).hom.app (Q₂.mapDerivedCategory.obj M) := by
  have hi (N : A₂) : e₀₂.inv.app N ≫ Q₀.map (r.inv.app N) =
      t.inv.app (Q₂.obj N) ≫ U₁₀.map (e₁₂.inv.app N) ≫ e₀₁.inv.app (R₂₁.obj N) := by
    let z := Q₀.mapIso (r.symm.app N) ≪≫ e₀₁.app (R₂₁.obj N) ≪≫
      U₁₀.mapIso (e₁₂.app N) ≪≫ t.app (Q₂.obj N)
    have hz : e₀₂.app N = z := Iso.ext (he N)
    have hh := congrArg Iso.inv hz
    dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
    rw [hh]
    simp only [Category.assoc, ← Q₀.map_comp, Iso.hom_inv_id_app, Q₀.map_id,
      Category.comp_id]
  have h := Functor.mapDerivedCategorySquareIso_hom_app_comp
    e₁₂.symm e₀₁.symm e₀₂.symm t.symm r.symm hi M
  apply (cancel_epi ((Functor.mapDerivedCategorySquareIso e₀₂).inv.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Category.assoc, Iso.symm_inv] at h ⊢
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]; rfl

private theorem transport_chain
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (R₁₀ : A₁ ⥤ A₀) (R₂₁ : A₂ ⥤ A₁) (R₂₀ : A₂ ⥤ A₀)
    (U₁₀ : B₁ ⥤ B₀) (U₂₁ : B₂ ⥤ B₁) (U₂₀ : B₂ ⥤ B₀)
    {Q₀ q₀ : A₀ ⥤ B₀} {Q₁ q₁ : A₁ ⥤ B₁} {Q₂ q₂ : A₂ ⥤ B₂}
    (a₀ : Q₀ ≅ q₀) (a₁ : Q₁ ≅ q₁) (a₂ : Q₂ ≅ q₂)
    (e₀₁ : R₁₀ ⋙ q₀ ≅ q₁ ⋙ U₁₀) (e₁₂ : R₂₁ ⋙ q₁ ≅ q₂ ⋙ U₂₁)
    (e₀₂ : R₂₀ ⋙ q₀ ≅ q₂ ⋙ U₂₀)
    (r : R₂₁ ⋙ R₁₀ ≅ R₂₀) (t : U₂₁ ⋙ U₁₀ ≅ U₂₀)
    (he : ∀ M, e₀₂.hom.app M = q₀.map (r.inv.app M) ≫
      e₀₁.hom.app (R₂₁.obj M) ≫ U₁₀.map (e₁₂.hom.app M) ≫ t.hom.app (q₂.obj M))
    (M : A₂) :
    (Functor.isoWhiskerLeft R₂₀ a₀ ≪≫ e₀₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₀).hom.app M = Q₀.map (r.inv.app M) ≫
    (Functor.isoWhiskerLeft R₁₀ a₀ ≪≫ e₀₁ ≪≫
      Functor.isoWhiskerRight a₁.symm U₁₀).hom.app (R₂₁.obj M) ≫
    U₁₀.map ((Functor.isoWhiskerLeft R₂₁ a₁ ≪≫ e₁₂ ≪≫
      Functor.isoWhiskerRight a₂.symm U₂₁).hom.app M) ≫ t.hom.app (Q₂.obj M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (a₀.hom.naturality (r.inv.app M)), he]
  slice_rhs 4 5 => rw [← U₁₀.map_comp, Iso.inv_hom_id_app, U₁₀.map_id]
  simp only [Category.assoc]
  rw [← t.hom.naturality]
  simp only [Functor.comp_map]
  erw [Category.id_comp]

namespace AlgebraicGeometry.Etale
private theorem e_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map ((upperStarRestrictScalarsIsoSheaf φ f).hom.app M) =
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom) M
  have hm := underived_mate φ f
  rw [hm] at h
  simpa [lowerStarRestrictScalarsIso] using h.symm

private theorem e_chain {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) :
    (upperStarRestrictScalarsIsoSheaf (ψ.comp φ) f).hom.app M =
      (upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        ((upperStarRestrictScalarsIsoSheaf ψ f).hom.app M) ≫
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((upperStar (ModuleCat.{u + 1} C) f).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [e_unit]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  erw [reassoc_of% (e_unit φ f ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M)) ≫
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIsoSheaf ψ f).hom.app M)) ≫ _
  rw [← Functor.map_comp_assoc, e_unit]
  ext U x
  rfl
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private theorem underived_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom)) =
        𝟙 (lowerStar (ModuleCat.{u + 1} B) f ⋙
          Sheaf.restrictScalars (Scheme.ProEt.topology X) φ) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)).injective
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [upperStarRestrictScalarsIso, conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom,
    TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback
        @WeaklyEtale ⊤ f).obj U)))).symm
private theorem e_unit {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).map ((upperStarRestrictScalarsIso φ f).hom.app M) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  have h := unit_mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ f).hom) M
  have hm := underived_mate φ f
  rw [hm] at h
  simpa using h.symm

private theorem e_chain {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)) :
    (upperStarRestrictScalarsIso (ψ.comp φ) f).hom.app M =
      (upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (upperStarRestrictScalarsIso φ f).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M) ≫
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl).hom.app
        ((upperStar (ModuleCat.{u + 1} C) f).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [e_unit]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  erw [reassoc_of% (e_unit φ f ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ).obj M)) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
      ((lowerStar (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIso ψ f).hom.app M)) ≫ _
  rw [← Functor.map_comp_assoc, e_unit]
  ext U x
  rfl
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale
private theorem scalarRestriction_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C))) :
    (scalarRestrictionPullbackIso (ψ.comp φ) f).hom.app M =
      (L(upperStar (ModuleCat.{u + 1} A) f)).map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
          (f := φ) (g := ψ)).inv.app M) ≫
      (scalarRestrictionPullbackIso φ f).hom.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        ((scalarRestrictionPullbackIso ψ f).hom.app M) ≫
      (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl
        (f := φ) (g := ψ)).hom.app ((L(upperStar (ModuleCat.{u + 1} C) f)).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  exact transport_chain _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} C) f)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f))
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf ψ f))
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf (ψ.comp φ) f))
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl)
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl)
    (derive_chain _ _ _ _ _ _ _ _ _
      (upperStarRestrictScalarsIsoSheaf φ f) (upperStarRestrictScalarsIsoSheaf ψ f)
      (upperStarRestrictScalarsIsoSheaf (ψ.comp φ) f)
      (Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
      (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
      (e_chain φ ψ f)) M
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale
private theorem scalarRestriction_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))) :
    (leftDerivedUpperStarRestrictScalarsIso.{u} (ψ.comp φ) f).hom.app M =
      ((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f))).map
        ((Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl
          (f := φ) (g := ψ)).inv.app M) ≫
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ f).hom.app
        ((Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ).obj M) ≫
      (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ).map
        ((leftDerivedUpperStarRestrictScalarsIso.{u} ψ f).hom.app M) ≫
      (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl
        (f := φ) (g := ψ)).hom.app (((Functor.leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 1,
          u + 1}
        (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f))).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact @transport_chain.{u + 2, u + 2, u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} C)))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) (ψ.comp φ))
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) ψ)
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) (ψ.comp φ))
    _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory.{u + 2, u} (ModuleCat.{u + 1} C) f)
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso φ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso ψ f))
    (Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (upperStarRestrictScalarsIso (ψ.comp
        φ) f))
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology X) rfl)
    (Sheaf.derivedRestrictScalarsCompIso.{u} (Scheme.ProEt.topology T) rfl)
    (derive_chain.{u + 1}
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) (ψ.comp φ))
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) ψ)
      (Sheaf.restrictScalars (Scheme.ProEt.topology T) (ψ.comp φ))
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} A) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} B) f)
      (upperStar.{u + 2, u} (ModuleCat.{u + 1} C) f)
      (upperStarRestrictScalarsIso φ f) (upperStarRestrictScalarsIso ψ f)
      (upperStarRestrictScalarsIso (ψ.comp φ) f)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl)
      (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl)
      (e_chain φ ψ f)) M
end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Etale
private theorem scalarPullback_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.scalarPullbackEtaleIso (ψ.comp φ) f).hom.app M =
      (L(upperStar (ModuleCat.{u + 1} C) f)).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).inv.app M) ≫
      (ProEtale.scalarPullbackEtaleIso ψ f).hom.app
        ((ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj M) ≫
      (ProEtale.pbcFixedScalarExtension T.smallEtaleTopology ψ).map
        ((ProEtale.scalarPullbackEtaleIso φ f).hom.app M) ≫
      (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ
        (ψ.comp φ) rfl).hom.app ((L(upperStar (ModuleCat.{u + 1} A) f)).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let := ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology φ
  let := ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology ψ
  let := ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology (ψ.comp φ)
  let := ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
  let := ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology ψ
  let := ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology (ψ.comp φ)
  let a₀₁ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let a₁₂ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ)
  let a₀₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology (ψ.comp φ))
  let b₀₁ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let b₁₂ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ)
  let b₀₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (ψ.comp φ))
  let kφ := ProEtale.scalarPullbackReverseEtale φ f
  let kψ := ProEtale.scalarPullbackReverseEtale ψ f
  let kχ := ProEtale.scalarPullbackReverseEtale (ψ.comp φ) f
  have : IsIso kφ := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have : IsIso kψ := (ProEtale.scalarPullbackReverse_isIso ψ f).2
  have : IsIso kχ := (ProEtale.scalarPullbackReverse_isIso (ψ.comp φ) f).2
  let cx := ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  let ct := ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  have hk := reverse_chain a₀₁ a₁₂ a₀₂ b₀₁ b₁₂ b₀₂
    (L(upperStar (ModuleCat.{u + 1} A) f)) (L(upperStar (ModuleCat.{u + 1} B) f))
    (L(upperStar (ModuleCat.{u + 1} C) f))
    (scalarRestrictionPullbackIso φ f).hom (scalarRestrictionPullbackIso ψ f).hom
    (scalarRestrictionPullbackIso (ψ.comp φ) f).hom
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl)
    (Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology rfl)
    (scalarRestriction_chain φ ψ f) M
  let z := ct.symm.app ((L(upperStar (ModuleCat.{u + 1} A) f)).obj M) ≪≫
    (ProEtale.pbcFixedScalarExtension T.smallEtaleTopology ψ).mapIso ((asIso kφ).app M) ≪≫
    (asIso kψ).app ((ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ).obj M) ≪≫
    (L(upperStar (ModuleCat.{u + 1} C) f)).mapIso (cx.app M)
  have hz : (asIso kχ).app M = z := Iso.ext hk
  have hh := congrArg Iso.inv hz
  dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
  simpa only [Category.assoc, ProEtale.scalarPullbackEtaleIso_eq_fromMate,
    ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom] using hh

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.ProEtale
private theorem scalarPullback_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.scalarPullbackProEtaleIso (ψ.comp φ) f).hom.app M =
      (L(upperStar (ModuleCat.{u + 1} C) f)).map
        ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ
          (ψ.comp φ) rfl).inv.app M) ≫
      (ProEtale.scalarPullbackProEtaleIso ψ f).hom.app
        ((ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj M) ≫
      (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) ψ).map
        ((ProEtale.scalarPullbackProEtaleIso φ f).hom.app M) ≫
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology T) φ ψ
        (ψ.comp φ) rfl).hom.app ((L(upperStar (ModuleCat.{u + 1} A) f)).obj M) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) φ
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) ψ
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) (ψ.comp φ)
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) φ
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) ψ
  let := ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) (ψ.comp φ)
  let a₀₁ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X)
    φ)
  let a₁₂ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X)
    ψ)
  let a₀₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) (ψ.comp φ))
  let b₀₁ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T)
    φ)
  let b₁₂ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T)
    ψ)
  let b₀₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) (ψ.comp φ))
  let kφ := ProEtale.scalarPullbackReverseProEtale φ f
  let kψ := ProEtale.scalarPullbackReverseProEtale ψ f
  let kχ := ProEtale.scalarPullbackReverseProEtale (ψ.comp φ) f
  have : IsIso kφ := (ProEtale.scalarPullbackReverse_isIso φ f).1
  have : IsIso kψ := (ProEtale.scalarPullbackReverse_isIso ψ f).1
  have : IsIso kχ := (ProEtale.scalarPullbackReverse_isIso (ψ.comp φ) f).1
  let cx := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl
  let ct := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl
  have hk := reverse_chain a₀₁ a₁₂ a₀₂ b₀₁ b₁₂ b₀₂
    (L(upperStar (ModuleCat.{u + 1} A) f)) (L(upperStar (ModuleCat.{u + 1} B) f))
    (L(upperStar (ModuleCat.{u + 1} C) f))
    (leftDerivedUpperStarRestrictScalarsIso φ f).hom (leftDerivedUpperStarRestrictScalarsIso ψ
      f).hom
    (leftDerivedUpperStarRestrictScalarsIso (ψ.comp φ) f).hom
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology X) rfl)
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) rfl)
    (scalarRestriction_chain φ ψ f) M
  let z := ct.symm.app ((L(upperStar (ModuleCat.{u + 1} A) f)).obj M) ≪≫
    (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) ψ).mapIso ((asIso kφ).app M) ≪≫
    (asIso kψ).app ((ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj M) ≪≫
    (L(upperStar (ModuleCat.{u + 1} C) f)).mapIso (cx.app M)
  have hz : (asIso kχ).app M = z := Iso.ext hk
  have hh := congrArg Iso.inv hz
  dsimp only [z, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at hh
  simpa only [Category.assoc, ProEtale.scalarPullbackProEtaleIso, Iso.symm_hom] using hh

end AlgebraicGeometry.ProEtale

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint
end CoefficientChainHelpers

namespace AlgebraicGeometry.Etale

/-- Naturality of the specified coefficient projection, as an equality in D(X,B).
Source: blueprint order 2130, naturality clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: take B-geometric transposes. Naturality of the A-counit and the scalar units
makes the two scalar-unit precomposites equal. The scalar-adjunction bijection and
then the B-geometric adjunction bijection are injective, proving the equality. -/
theorem finiteCoefficientDirectImageMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    {K L : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) φ).map ((R(lowerStar
        (ModuleCat.{u + 1} A) f)).map h) ≫
        finiteCoefficientDirectImageMap φ f L =
      finiteCoefficientDirectImageMap φ f K ≫
        (R(lowerStar (ModuleCat.{u + 1} B) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).map h) :=
            by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  refine coefficient_naturality _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2
    (finiteCoefficientDirectImageMap φ f) ?_ h
  · intro K d hd
    exact (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.2 d hd

private theorem finiteCoefficientDirectImageMap_eq_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    finiteCoefficientDirectImageMap φ f K =
      (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
        (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackEtaleIso φ f).hom)).app K := by
  rw [ProEtale.scalarPullbackEtaleIso_eq_fromMate]
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  exact coefficient_eq_mate _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2
    K _ (fun d hd ↦ (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.2 d hd)

private theorem scalarExtension_lowerBound
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a b : ℤ) (hTor : DerivedCategory.hasTorAmplitudeIn A T a b K) :
    ((scalarExtension φ T).obj K).IsGE a := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  apply (_root_.DerivedCategory.isGE_iff _ a).2
  intro i hi
  apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
  exact (hTor (scalarCoefficientSheaf φ T) i (.inl hi)).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso ((scalarTensorIso φ T).app K))

private theorem finiteCoefficientRestrictionPullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    finiteCoefficientRestrictionPullback φ f = leftDerivedUpperStarRestrictScalarsIso φ f := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  have h : upperStarRestrictScalarsIsoSheaf φ f = upperStarRestrictScalarsIso φ f := by
    apply Iso.ext
    apply (conjugateEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
        (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ))
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).injective
    rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
    simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq,
      Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv]
    exact (conjugateEquiv _ _).apply_symm_apply _
  simp only [finiteCoefficientRestrictionPullback, leftDerivedUpperStarRestrictScalarsIso, h]

private theorem scalarRestrictionPullbackIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    scalarRestrictionPullbackIso φ f = leftDerivedUpperStarRestrictScalarsIso φ f :=
  finiteCoefficientRestrictionPullback_eq φ f

private theorem composition_rightAdjointUniq
    (A : Type (u + 1)) [CommRing A]
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y) :
    (Adjunction.rightAdjointUniq
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g)).ofNatIsoLeft
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).inv := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  rw [rightAdjointUniq_ofNatIsoLeft_hom]
  have hc : conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g) =
      rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g := by
    apply Iso.ext
    exact conjugateEquiv_leftDerivedUpperStarComp_hom
      (ModuleCat.{u + 1} A) f g (f ≫ g) rfl
  exact congrArg Iso.inv hc

attribute [local irreducible] upperStar
attribute [-instance] ProEtale.pbcRestriction_isRightAdjoint

/-- Geometric composition coherence, with the canonical direct-image compositors.
Source: blueprint order 2130, composition clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: the canonical compositor is normalized by the pasted inverse-image adjunction.
Take the B-coefficient composite geometric transpose. The one-step map transposes to
scalar extension of the pasted A-counit. For the two-step map, counit naturality
moves c_f past the g-counit; the defining transpose equations for c_g and c_f reduce
it to that same scalar extension of the pasted A-counit. The injectivity of the
B-coefficient adjunction gives equality, without faithfulness of scalar restriction. -/
theorem finiteCoefficientDirectImageMap_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    finiteCoefficientDirectImageMap φ (f ≫ g) K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Y.smallEtaleTopology) φ).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).symm.hom.app K) ≫
        finiteCoefficientDirectImageMap φ g ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) g)).map (finiteCoefficientDirectImageMap φ f K) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) f g).symm.inv.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (T.smallEtaleTopology) φ).obj K) :=
            by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let := ProEtale.pbcRestriction_isRightAdjoint Y.smallEtaleTopology φ
  let := ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology φ
  let := ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let kf := ProEtale.scalarPullbackReverseEtale φ g
  let kg := ProEtale.scalarPullbackReverseEtale φ f
  let kh := ProEtale.scalarPullbackReverseEtale φ (f ≫ g)
  have hf : IsIso kf := (ProEtale.scalarPullbackReverse_isIso φ g).2
  have hg : IsIso kg := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have hh : IsIso kh := (ProEtale.scalarPullbackReverse_isIso φ (f ≫ g)).2
  have hEx : Adjunction.ExchangeCompCompatible kf kg kh
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g) := by
    dsimp only [kf, kg, kh, ProEtale.scalarPullbackReverseEtale]
    refine reverse_mate_comp ay ax adt
      (scalarRestrictionPullbackIso φ g)
      (scalarRestrictionPullbackIso φ f)
      (scalarRestrictionPullbackIso φ (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g) ?_
    intro M
    simpa only [scalarRestrictionPullbackIso_eq] using
      leftDerivedUpperStarRestrictScalarsIso_comp_hom_app φ f g M
  have h := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (f ≫ g))
    kf kg kh (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g) hEx K
  rw [composition_rightAdjointUniq, composition_rightAdjointUniq] at h
  have h' := congrArg
    (fun m ↦ m ≫ (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) f g).hom.app
      ((ProEtale.pbcFixedScalarExtension T.smallEtaleTopology φ).obj K)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h'
  erw [Category.comp_id] at h'
  rw [finiteCoefficientDirectImageMap_eq_mate, finiteCoefficientDirectImageMap_eq_mate,
    finiteCoefficientDirectImageMap_eq_mate]
  simpa only [ProEtale.scalarPullbackEtaleIso_eq_fromMate,
    ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom, Iso.symm_inv, asIso_inv,
    kf, kg, kh] using h'.symm

attribute [instance] ProEtale.pbcRestriction_isRightAdjoint

attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

/-- Successive coefficient changes, including nonquotient maps and identity changes.
Source: blueprint order 2130, coefficient-chain clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: take C-geometric transposes. The B-to-C defining equation followed by
naturality reduces the two-step transpose to S_BC(S_AB(ε_A)). On flat K-flat models,
the scalar compositor is (x tensor b) tensor c ↦ x tensor φ(b)c, with inverse
x tensor c ↦ (x tensor 1) tensor c. Its compatibility with the same pullback
balancing map identifies this with S_AC(ε_A). Injectivity of the C-geometric
adjunction proves equality in D(C). There is no requirement that B be an A_E,m. -/
theorem finiteCoefficientDirectImageMap_coefficientChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    finiteCoefficientDirectImageMap (ψ.comp φ) f K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (X.smallEtaleTopology) φ ψ (ψ.comp φ) rfl).inv.app ((R(lowerStar (ModuleCat.{u + 1} A)
            f)).obj K) ≫
        (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (X.smallEtaleTopology) ψ).map
          (finiteCoefficientDirectImageMap φ f K) ≫
        finiteCoefficientDirectImageMap ψ f ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
          (T.smallEtaleTopology) φ).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} C) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (T.smallEtaleTopology) φ ψ (ψ.comp φ) rfl).hom.app K) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology φ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology ψ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint X.smallEtaleTopology (ψ.comp φ)
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology ψ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology (ψ.comp φ)
  rw [finiteCoefficientDirectImageMap_eq_mate, finiteCoefficientDirectImageMap_eq_mate,
    finiteCoefficientDirectImageMap_eq_mate]
  exact mate_chain
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) f)
    (ProEtale.scalarPullbackEtaleIso φ f).hom (ProEtale.scalarPullbackEtaleIso ψ f).hom
    (ProEtale.scalarPullbackEtaleIso (ψ.comp φ) f).hom
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (scalarPullback_chain φ ψ f) K

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Naturality of the specified coefficient projection, as an equality in D(X,B).
Source: blueprint order 2130, naturality clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: take B-geometric transposes. Naturality of the A-counit and the scalar units
makes the two scalar-unit precomposites equal. The scalar-adjunction bijection and
then the B-geometric adjunction bijection are injective, proving the equality. -/
theorem finiteCoefficientDirectImageMap_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L) :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).map h) ≫
        finiteCoefficientChangeDirectImageMap φ f L =
      finiteCoefficientChangeDirectImageMap φ f K ≫
        (R(lowerStar (ModuleCat.{u + 1} B) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).map h)
          := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let aa := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f
  let ab := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let e := leftDerivedUpperStarRestrictScalarsIso.{u} φ f
  have hk := (scalarPullbackReverse_isIso.{u} φ f).1
  have hu (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
      (d : (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj M) ⟶
        (R(lowerStar (ModuleCat.{u + 1} B) f)).obj
          ((pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj M))
      (hd : IsFiniteCoefficientDirectImageMap φ f M d) :
      d = finiteCoefficientChangeDirectImageMap φ f M :=
    (finiteCoefficientDirectImageMap_existsUnique φ f M).choose_spec.2 d hd
  have hn := @coefficient_naturality.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    inferInstance inferInstance inferInstance inferInstance
    _ _ aa _ _ ab _ _ ax _ _ adt e hk
    (finiteCoefficientChangeDirectImageMap φ f) hu K L h
  exact hn

attribute [local irreducible] upperStar
attribute [-instance] pbcRestriction_isRightAdjoint

private theorem mapDerivedAdjunction_eq
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapDerivedCategoryRightDerivedAdjunction
      =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  refine ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up
    ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ?_
  ext C
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

private theorem conjugate_leftDerivedUpperStarComp_hom
    (A : Type (u + 1)) [CommRing A] {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y) :
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom =
    conjugateEquiv
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        g).mapDerivedCategoryRightDerivedAdjunction).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          f).mapDerivedCategoryRightDerivedAdjunction)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫
        g)).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).hom := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  rw [mapDerivedAdjunction_eq, mapDerivedAdjunction_eq, mapDerivedAdjunction_eq]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

private theorem finiteDirectImageComposition_conjugate
    (A : Type (u + 1)) [CommRing A] {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y) :
    (finiteDirectImageComposition A f g).inv =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  rw [conjugate_leftDerivedUpperStarComp_hom]
  apply Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
  have hi : conjugateIsoEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (upperStarComp (ModuleCat.{u + 1} A) f g).symm =
      (lowerStarComp (ModuleCat.{u + 1} A) f g).symm :=
    Iso.ext (coefficient_conjugateEquiv_upperStarComp_inv (ModuleCat.{u + 1} A) f g)
  exact (congrArg Iso.inv hi).symm

private theorem finiteCoefficientDirectImageMap_eq_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    finiteCoefficientChangeDirectImageMap φ f K =
      (mateEquiv.{u + 1, u + 1, u + 1, u + 1,
          u + 2, u + 2, u + 2, u + 2}
        (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f)
        (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f)
        (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso.{u} φ f).hom)).app K := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) φ
  let := pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) φ
  let aa := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f
  let ab := derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let e := leftDerivedUpperStarRestrictScalarsIso.{u} φ f
  have hk := (scalarPullbackReverse_isIso.{u} φ f).1
  exact @coefficient_eq_mate.{u + 2, u + 2, u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1}
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    inferInstance inferInstance inferInstance inferInstance
    _ _ aa _ _ ab _ _ ax _ _ adt e hk K _
    (fun d hd ↦ (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.2 d hd)

private theorem finiteCoefficientDirectImageMap_etaleOrigin_isIso_of_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A T)
    (hKge : ∃ c : ℤ, K.IsGE c)
    (hBge : ∃ c : ℤ, ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K).IsGE c)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ f K)] :
    IsIso (finiteCoefficientChangeDirectImageMap φ f
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) f)).map
          ((pbcComparisonReduction T φ).hom.app K)) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  have he := etaleProEtale_scalar_mate.{u} φ f K hKge hBge
  rw [← finiteCoefficientDirectImageMap_eq_mate φ f
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K),
    ← Etale.finiteCoefficientDirectImageMap_eq_mate φ f K] at he
  have := directImageComparisonAmbient_isIso B f
    ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) hBge
  rw [he]
  infer_instance

attribute [instance] pbcRestriction_isRightAdjoint

attribute [-instance] pbcRestriction_isRightAdjoint

private theorem composition_rightAdjointUniq
    (A : Type (u + 1)) [CommRing A]
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y) :
    (Adjunction.rightAdjointUniq
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g)).ofNatIsoLeft
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).hom =
      (finiteDirectImageComposition A f g).hom := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  rw [rightAdjointUniq_ofNatIsoLeft_hom]
  have hc : conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g) =
      (finiteDirectImageComposition A f g).symm := by
    exact Iso.ext (finiteDirectImageComposition_conjugate A f g).symm
  exact congrArg Iso.inv hc

/-- Geometric composition coherence, with the canonical direct-image compositors.
Source: blueprint order 2130, composition clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: the canonical compositor is normalized by the pasted inverse-image adjunction.
Take the B-coefficient composite geometric transpose. The one-step map transposes to
scalar extension of the pasted A-counit. For the two-step map, counit naturality
moves c_f past the g-counit; the defining transpose equations for c_g and c_f reduce
it to that same scalar extension of the pasted A-counit. The injectivity of the
B-coefficient adjunction gives equality, without faithfulness of scalar restriction. -/
theorem finiteCoefficientDirectImageMap_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    finiteCoefficientChangeDirectImageMap φ (f ≫ g) K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology Y) φ).map
        ((finiteDirectImageComposition A f g).hom.app K) ≫
        finiteCoefficientChangeDirectImageMap φ g ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} B) g)).map (finiteCoefficientChangeDirectImageMap φ f K) ≫
        (finiteDirectImageComposition B f g).inv.app
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K)
          := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology Y) φ
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology X) φ
  let := pbcRestriction_isRightAdjoint.{u} (Scheme.ProEt.topology T) φ
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology Y) φ)
  let ax := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology X) φ)
  let adt := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (Scheme.ProEt.topology T) φ)
  let kf := scalarPullbackReverseProEtale.{u} φ g
  let kg := scalarPullbackReverseProEtale.{u} φ f
  let kh := scalarPullbackReverseProEtale.{u} φ (f ≫ g)
  have hf : IsIso kf := (ProEtale.scalarPullbackReverse_isIso.{u} φ g).1
  have hg : IsIso kg := (ProEtale.scalarPullbackReverse_isIso.{u} φ f).1
  have hh : IsIso kh := (ProEtale.scalarPullbackReverse_isIso.{u} φ (f ≫ g)).1
  have hEx : Adjunction.ExchangeCompCompatible kf kg kh
      (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} B) f g) := by
    dsimp only [kf, kg, kh, scalarPullbackReverseProEtale]
    refine @reverse_mate_comp
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      _ _ ay _ _ ax _ _ adt _ _ _ _ _ _
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ g)
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ f)
      (leftDerivedUpperStarRestrictScalarsIso.{u} φ (f ≫ g))
      (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} B) f g) ?_
    intro M
    exact
      leftDerivedUpperStarRestrictScalarsIso_comp_hom_app φ f g M
  have h := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) g)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) (f ≫ g))
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) g)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) (f ≫ g))
    kf kg kh (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} A) f g)
      (leftDerivedUpperStarComp.{u + 2, u} (ModuleCat.{u + 1} B) f g) hEx K
  rw [composition_rightAdjointUniq, composition_rightAdjointUniq] at h
  have h' := congrArg
    (fun m ↦ m ≫ (finiteDirectImageComposition B f g).inv.app
      ((ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology T) φ).obj K)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at h'
  erw [Category.comp_id] at h'
  rw [finiteCoefficientDirectImageMap_eq_mate, finiteCoefficientDirectImageMap_eq_mate,
    finiteCoefficientDirectImageMap_eq_mate]
  exact h'.symm

attribute [instance] pbcRestriction_isRightAdjoint

attribute [-instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

/-- Successive coefficient changes, including nonquotient maps and identity changes.
Source: blueprint order 2130, coefficient-chain clause and proof Step 3
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: take C-geometric transposes. The B-to-C defining equation followed by
naturality reduces the two-step transpose to S_BC(S_AB(ε_A)). On flat K-flat models,
the scalar compositor is (x tensor b) tensor c ↦ x tensor φ(b)c, with inverse
x tensor c ↦ (x tensor 1) tensor c. Its compatibility with the same pullback
balancing map identifies this with S_AC(ε_A). Injectivity of the C-geometric
adjunction proves equality in D(C). There is no requirement that B be an A_E,m. -/
theorem finiteCoefficientDirectImageMap_coefficientChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    finiteCoefficientChangeDirectImageMap (ψ.comp φ) f K =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl).inv.app ((R(lowerStar (ModuleCat.{u + 1} A)
            f)).obj K) ≫
        (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) ψ).map
          (finiteCoefficientChangeDirectImageMap φ f K) ≫
        finiteCoefficientChangeDirectImageMap ψ f
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
            (Scheme.ProEt.topology T) φ).obj K) ≫
        (R(lowerStar (ModuleCat.{u + 1} C) f)).map
          ((AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl).hom.app K) := by
  have := @cachedEtaleGroth.{u}
  have := @cachedEtaleSheafify.{u}
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) φ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) ψ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology X) (ψ.comp
    φ)
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) φ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) ψ
  let := AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint (Scheme.ProEt.topology T) (ψ.comp
    φ)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  rw [finiteCoefficientDirectImageMap_eq_mate, finiteCoefficientDirectImageMap_eq_mate,
    finiteCoefficientDirectImageMap_eq_mate]
  exact mate_chain
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction.{u + 2, u} (ModuleCat.{u + 1} C) f)
    (ProEtale.scalarPullbackProEtaleIso φ f).hom (ProEtale.scalarPullbackProEtaleIso ψ f).hom
    (ProEtale.scalarPullbackProEtaleIso (ψ.comp φ) f).hom
    (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ (ψ.comp φ) rfl)
    (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology T) φ ψ (ψ.comp φ) rfl)
    (scalarPullback_chain φ ψ f) K

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

end AlgebraicGeometry.ProEtale

section FinalCoefficientIsoHelpers

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

namespace AlgebraicGeometry.Etale
private theorem scalarPullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ProEtale.scalarPullbackEtaleIso φ f = scalarPullbackIso φ f := rfl
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
attribute [local irreducible] upperStar lowerStar
attribute [-instance] ProEtale.pbcRestriction_isRightAdjoint
private def scalarCoefficientSheafIsoConstant
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarCoefficientSheaf φ T ≅
      (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)) := by
  exact (constantCommuteCompose T.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
    (ModuleCat.of B B)

private theorem scalar_projection_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    [Algebra A B] [Module.Finite A B]
    {k : Type u} [Field k] [IsSepClosed k]
    {T X : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [LocallyOfFiniteType aX]
    (f : T ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f] (hf : f ≫ aX = aT)
    (K : DerivedCategoryModule A T)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      (scalarCoefficient (algebraMap A B) X)) := by
  have : IsNoetherianRing A := inferInstance
  let M := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  have : Finite B := Module.finite_of_finite A
  have : Finite M := inferInstanceAs (Finite B)
  have : Module.Finite A M := inferInstance
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aT
  have hcd := hasUniformDirectImageVanishingLE_two_mul A f aT aX hf d hd
  have hp := finiteConstantProjectionComponent_isIso A f (2 * d)
    (fun F q hq ↦ by
      have h := hcd F q (by exact_mod_cast hq)
      exact h.of_iso (homologyRightDerivedLowerStarSingleIsoHigherDirectImage A f F q))
    K hK M
  let e : scalarCoefficient (algebraMap A B) X ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) :=
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
    (scalarCoefficientSheafIsoConstant (algebraMap A B) X)
  exact (NatTrans.isIso_app_iff_of_iso
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K) e).2 hp
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
attribute [local irreducible] upperStar
private theorem restriction_exact_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    scalarRestrictionDirectImageMap φ f =
      (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom)
        ) := by
  rw [mapDerivedUpperStarLowerStarAdjunction_eq, mapDerivedUpperStarLowerStarAdjunction_eq]
  ext K
  simp only [scalarRestrictionDirectImageMap, scalarRestrictionPullbackIso,
    mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.id_comp, Functor.comp_map,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]

private theorem map_iso_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {U V : D} (a : U ≅ V)
    (h : F.obj X = U := by rfl) (h' : F.obj Y = V := by rfl)
    (he : F.map e.hom = eqToHom h ≫ a.hom ≫ eqToHom h'.symm) :
    F.map e.inv = eqToHom h' ≫ a.inv ≫ eqToHom h.symm := by
  subst U; subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he ⊢
  apply (cancel_mono a.hom).1
  rw [← he, ← F.map_comp, e.inv_hom_id, F.map_id, he, a.inv_hom_id]

private theorem plus_square_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory.Plus.ι.map ((derivedUpperStarRestrictScalarsIso φ f).hom.app N) =
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom.app
        N.obj := by
  have hi := map_iso_inv _root_.DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryPlusCompIso
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (upperStar (ModuleCat.{u + 1} A) f)).app N)
    ((Functor.mapDerivedCategoryCompIso
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (upperStar (ModuleCat.{u + 1} A) f)).symm.app N.obj) rfl rfl
    (by simpa using (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (upperStar (ModuleCat.{u + 1} A) f) N))
  simp only [derivedUpperStarRestrictScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.map_comp,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  have hi' := hi
  simp only [Iso.app_inv, eqToHom_refl, Category.id_comp, Category.comp_id] at hi'
  rw [hi']
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_plus_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (N : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (scalarRestrictionDirectImageMap φ f).app N.obj =
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.inv.app N) ≫
      _root_.DerivedCategory.Plus.ι.map ((derivedLowerStarRestrictScalarsIso φ f).hom.app N) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj N) := by
  rw [restriction_exact_mate]
  rw [← derived_mate φ f]
  rw [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    ← Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.id_comp, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.id_comp, Category.comp_id]
  simp only [Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  erw [(lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.naturality]
  dsimp only [Functor.comp_map]
  have hnat := (lowerStar (ModuleCat.{u + 1} A)
    f).rightDerivedFunctorPlusCompatibility.inv.naturality
    ((derivedUpperStarRestrictScalarsIso φ f).hom.app
      ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlus.obj N))
  dsimp only [Functor.comp_map] at hnat
  erw [← reassoc_of% hnat]
  simp only [Iso.inv_hom_id_app_assoc]
  have hm {M M' : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))} (h : M ⟶ M') :
      _root_.DerivedCategory.Plus.ι.map
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map h) =
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (_root_.DerivedCategory.Plus.ι.map h) := rfl
  rw [hm, Adjunction.map_restrictFullyFaithful_counit_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
  simp only [Functor.map_comp, plus_square_hom]
  simp only [Iso.symm_inv, Iso.refl_inv, NatTrans.id_app, Functor.comp_obj]
  dsimp only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
  have ha : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedAdjunction.ofNatIsoLeft
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory =
      mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f := by
    simpa only [derivedUpperStarLowerStarAdjunction, leftDerivedUpperStarIsoMapDerivedCategory]
      using (mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} A) f).symm
  have hb : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).derivedAdjunction.ofNatIsoLeft
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctorIsoMapDerivedCategory =
      mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f := by
    simpa only [derivedUpperStarLowerStarAdjunction, leftDerivedUpperStarIsoMapDerivedCategory]
      using (mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} B) f).symm
  rw [ha, hb]
  erw [(mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.naturality_assoc]
  dsimp only [Functor.comp_map, Functor.id_map]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift]
  slice_rhs 2 3 =>
    rw [← Functor.map_comp]
    erw [(Functor.mapDerivedCategorySquareIso
      (upperStarRestrictScalarsIsoSheaf φ f)).hom.naturality]
    rw [Functor.map_comp]
  dsimp only [Functor.comp_map]
  simp only [← Functor.map_comp]
  simp only [Sheaf.derivedRestrictScalars, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem restriction_reflects_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : AlgebraicGeometry.Scheme.{u})
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (f : K ⟶ L) [IsIso ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map f)] :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryHomologyFunctorIso n)
      f).2 (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars X.smallEtaleTopology φ)

private theorem scalarMate_isIso_of_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : DerivedCategoryModule A T) (a c : ℤ) [K.IsGE c]
    [((scalarExtension φ T).obj K).IsGE a]
    [IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      (scalarCoefficient φ X))] :
    IsIso ((scalarMate φ f).app K) := by
  let sx := scalarExtension φ X
  let st := scalarExtension φ T
  let rx := Sheaf.derivedRestrictScalars X.smallEtaleTopology φ
  let rt := Sheaf.derivedRestrictScalars T.smallEtaleTopology φ
  let rf := R(lowerStar (ModuleCat.{u + 1} A) f)
  let t := (derivedTensor (ModuleCat.{u + 1} A) T).obj K
  have hrt : (rt.obj (st.obj K)).IsGE a :=
    (Sheaf.restrictScalars T.smallEtaleTopology φ).isGE_mapDerivedCategory_obj _ a
  have hr : (rf.obj (rt.obj (st.obj K))).IsGE a :=
    isGE_rightDerivedLowerStar_obj A f _ a
  let e : rx.obj (sx.obj (rf.obj K)) ≅ rf.obj (rt.obj (st.obj K)) :=
    (scalarTensorIso φ X).app (rf.obj K) ≪≫
      asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
        (scalarCoefficient φ X)) ≪≫
      rf.mapIso (t.mapIso (scalarCoefficientPullbackIso φ f) ≪≫ (scalarTensorIso φ T).symm.app K)
  have hm : (sx.obj (rf.obj K)).IsGE a := by
    have hres : (rx.obj (sx.obj (rf.obj K))).IsGE a :=
      _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a
    apply (_root_.DerivedCategory.isGE_iff _ a).2
    intro q hq
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
    exact (_root_.DerivedCategory.isGE_iff _ a).1 hres q hq
  let N : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) := ⟨st.obj K, ⟨a, inferInstance⟩⟩
  let M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) := ⟨sx.obj (rf.obj K), ⟨a, hm⟩⟩
  let J : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨K, ⟨c, inferInstance⟩⟩
  have hb : IsIso ((scalarRestrictionDirectImageMap φ f).app (st.obj K)) := by
    rw [show (st.obj K) = N.obj from rfl, restriction_plus_mate]
    infer_instance
  have hh := scalarMate_restrict_eq_projection φ f J ⟨N, rfl⟩ ⟨M, rfl⟩
  have he : IsIso (e.hom) := inferInstance
  have hc : IsIso (rx.map ((scalarMate φ f).app K) ≫
      (scalarRestrictionDirectImageMap φ f).app (st.obj K)) := by
    rw [hh]
    exact he
  have : IsIso (rx.map ((scalarMate φ f).app K)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hb hc
  exact restriction_reflects_iso φ X _

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
private theorem coefficientMap_isIso_of_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) (K : DerivedCategoryModule A T)
    (a c : ℤ) [K.IsGE c] [((scalarExtension φ T).obj K).IsGE a]
    [IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      (scalarCoefficient φ X))] : IsIso (finiteCoefficientDirectImageMap φ f K) := by
  rw [finiteCoefficientDirectImageMap_eq_mate, scalarPullback_eq]
  exact scalarMate_isIso_of_projection φ f K a c

private theorem coefficientMap_isIso_of_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    [Algebra A B] [Module.Finite A B]
    {k : Type u} [Field k] [IsSepClosed k]
    {T X : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [LocallyOfFiniteType aX]
    (f : T ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f] (hf : f ≫ aX = aT)
    (K : DerivedCategoryModule A T) (a c d : ℤ) [K.IsGE c]
    [((scalarExtension (algebraMap A B) T).obj K).IsGE a]
    (hK : ∀ q : ℤ, d < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
    IsIso (finiteCoefficientDirectImageMap (algebraMap A B) f K) := by
  have : IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      (scalarCoefficient (algebraMap A B) X)) :=
    scalar_projection_isIso (A := A) (B := B) aT aX f hf K ⟨d, hK⟩
  exact coefficientMap_isIso_of_projection (algebraMap A B) f K a c

end AlgebraicGeometry.Etale

end FinalCoefficientIsoHelpers

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

namespace AlgebraicGeometry.Etale

/-- Ordinary uncompleted finite coefficient change commutes with a separated
finite-type direct image on a bounded constructible complex of finite Tor amplitude.
No flatness of the finite algebra B over A is assumed.
Source: blueprint order 2130, etale isomorphism clause
(blueprint: lemma-change-coefficients-direct-image--1).

Proof: the positive-level coefficient ring is finite, hence Noetherian, and B is
finitely presented as a module over it. The finite-type source has finite Krull
dimension. The uniform all-sheaf cohomological-dimension bound over the separably
closed base field and the finite-constant projection theorem make the required
projection morphism invertible. Constant/restriction commutation identifies its
constant module with the scalar coefficient sheaf.

The normalized scalar/pullback comparison equals the inverse mate of the exact
restriction/pullback square, by their cochain scalar-unit equations. Tor amplitude
gives a lower bound for the scalar extension of K. The projection isomorphism and
faithful exact restriction give a lower bound for the scalar extension of Rf_*K.
Consequently all comparisons in the published projection/mate identity apply on
bounded-below representatives. The ambient restriction/direct-image mate is the
canonical bounded-below comparison, by the derived adjunction identities. Cancelling
it in the projection/mate identity makes restriction of the specified coefficient
map invertible. Faithful exact restriction reflects isomorphisms. -/
theorem finiteCoefficientDirectImageMap_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    (B : Type (u + 1)) [CommRing B]
    [Algebra (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    [Module.Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B]
    (T X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : T ⟶ X) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left)
    (_hK : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) T.left K)
    (_hTor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) T.left a b K) :
    IsIso (finiteCoefficientDirectImageMap
      (algebraMap (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) B) f.left K) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let φ : A →+* B := algebraMap A B
  have : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n hn)
  obtain ⟨c, d, hcd, hb⟩ := _hK.2
  have : K.IsGE c := (_root_.DerivedCategory.isGE_iff K c).2
    (fun q hq ↦ hb q (.inl hq))
  obtain ⟨a, b, hab, hTor⟩ := _hTor
  have : ((scalarExtension φ T.left).obj K).IsGE a :=
    scalarExtension_lowerBound φ T.left K a b hTor
  exact coefficientMap_isIso_of_geometry (A := A) (B := B) T.hom X.hom f.left
    (Over.w f) K a c d (fun q hq ↦ hb q (.inr hq))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar
attribute [-instance] pbcRestriction_isRightAdjoint

attribute [instance] pbcRestriction_isRightAdjoint

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

-- Keep the imported instance available to consumers of this module.
attribute [instance] WeilConjectures.scalarReductionSiteSmall
