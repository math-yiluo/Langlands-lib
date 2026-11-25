/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Signed shifts on the published site derived tensor

Source: Stacks Project, more-algebra.tex, Tag 0FNH, item-shift-tensor;
sites-cohomology.tex, Tags 06YS and 06YU; Categories, Tag 04VK.
(blueprint: lem-weil-pbc-derived-tensor-shift-descent)

The representative comparison is the published resolving comparison exposed by
`tensorDescentPair`. The predicates below spell out its normalization and the
universal fixed-comparison conclusion; they do not choose another tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

local instance (I : Type r) :
    Limits.HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

local instance (I : Type r) :
    Limits.HasColimitsOfShape (Discrete I) (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

local instance (I : Type) :
    Limits.HasColimitsOfShape (Discrete I) (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
  let : Limits.HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

/-- A transparent abbreviation of Mathlib's existing total tensor functor, exposing its
canonical signed shift instances. This is definitionally `SiteTensorComplexFunctor R`.
Source: Stacks, Tags 06YM and 0FNH
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
abbrev tensorShiftTotal :=
  (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).map₂CochainComplex

/-- The prescribed restriction of both shift comparisons to flat-term K-flat pairs.
This is the conjugation by the published representative comparison and the canonical
localization shift comparison, written without inverse arrows by clearing the two
invertible initial factors.
Source: Stacks, Tags 0FNH and 06YU
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorResolvingShiftCompatible
    (stable : ∀ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧))
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  ∀ (P S : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : TensorFlatRepresentative (J := J) (R := R) P)
    (hS : TensorFlatRepresentative (J := J) (R := R) S) (n : ℤ),
    ((tensorDescentPair (J := J) (R := R)
        (P⟦n⟧) S (stable P hP n) hS).hom ≫
        ((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).map (((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
            P) ≫
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).commShiftIso n).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₁Iso P S
            (MonoidalCategory.curriedTensor _) n).hom ≫
        ((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
          (((tensorShiftTotal (R := R)).obj P).obj S) ≫
        (tensorDescentPair (J := J) (R := R) P S hP hS).hom⟦n⟧') ∧
    ((tensorDescentPair (J := J) (R := R)
        P (S⟦n⟧) hP (stable S hS n)).hom ≫
        ((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).map (((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
            S) ≫
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).commShiftIso n).hom.app (DerivedCategory.Q.obj S) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₂Iso P S
            (MonoidalCategory.curriedTensor _) n).hom ≫
        ((DerivedCategory.Q (C := ringedSiteModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).commShiftIso n).hom.app
          (((tensorShiftTotal (R := R)).obj P).obj S) ≫
        (tensorDescentPair (J := J) (R := R) P S hP hS).hom⟦n⟧')

/-- Every fixed-factor comparison normalized on resolving objects respects the signed shifts.
The natural isomorphisms are pulled back to complexes along the full homotopy quotient.
Thus their naturality is exactly naturality on the homotopy category; the quotient's
canonical shift comparison identifies these squares with the homotopy-level squares.
`NatTrans.CommShift` says that the given shifts coincide with the shifts descended in
one variable under this factorization.
Source: Stacks, Tags 06YS, 06YU and 04VK
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorFixedComparisonsShiftCompatible
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  ∀ (A : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hA : TensorFlatRepresentative (J := J) (R := R) A),
    (∀ (B B' : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : B ⟶ B'),
      QuasiIso f → QuasiIso (((tensorShiftTotal (R := R)).obj A).map f) ∧
        QuasiIso (((tensorShiftTotal (R := R)).flip.obj A).map f)) →
    (∀ eL : (tensorShiftTotal (R := R)).obj A ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj A),
      (∀ (B : CochainComplex (ringedSiteModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
        (hB : TensorFlatRepresentative (J := J) (R := R) B),
        eL.app B = tensorDescentPair (J := J) (R := R) A B hA hB) → NatTrans.CommShift eL.hom ℤ) ∧
    (∀ eR : (tensorShiftTotal (R := R)).flip.obj A ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj A),
      (∀ (B : CochainComplex (ringedSiteModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
        (hB : TensorFlatRepresentative (J := J) (R := R) B),
        eR.app B = tensorDescentPair (J := J) (R := R) B A hB hA) → NatTrans.CommShift eR.hom ℤ)

/-- Uniqueness of the normalized natural isomorphisms themselves, without assuming
coherence laws on a competing isomorphism. Once the restriction of a candidate agrees
with the prescribed shifts on resolving pairs, all of its components agree.
Source: Stacks, Tag 04VK, and the arbitrary-transformation clause of tensor descent
(blueprint: lem-weil-pbc-derived-tensor-shift-descent). -/
def tensorShiftComparisonsUnique
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int) : Prop :=
  letI := s
  (∀ (n : ℤ)
    (α : (shiftFunctor _ n).prod (𝟭 _) ⋙
        siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
      siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ⋙ shiftFunctor _ n),
    (∀ (P S : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      TensorFlatRepresentative (J := J) (R := R) S →
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj S)).commShiftIso n).hom.app (DerivedCategory.Q.obj P)) →
    ∀ (M N : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
      α.hom.app (M, N) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj N).commShiftIso n).hom.app M) ∧
  (∀ (n : ℤ)
    (α : (𝟭 _).prod (shiftFunctor _ n) ⋙
        siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
      siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ⋙ shiftFunctor _ n),
    (∀ (P S : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      TensorFlatRepresentative (J := J) (R := R) S →
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj
          (DerivedCategory.Q.obj P)).commShiftIso n).hom.app (DerivedCategory.Q.obj S)) →
    ∀ (M N : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
      α.hom.app (M, N) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).obj M).commShiftIso n).hom.app N)

private theorem quotientCompQh_hom
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app P = 𝟙 _ := rfl

private theorem quotientCompQh_inv
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app P = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem Q_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {P S : CochainComplex A ℤ} (f : P ⟶ S) :
    DerivedCategory.Q.map f =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) := by
  simpa only [quotientCompQh_inv, Category.id_comp, Category.comp_id] using
    DerivedCategory.quotientCompQhIso_inv_naturality f

section
open CategoryTheory.Functor
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] HasShift.quotient ObjectProperty.hasShift
  Quotient.functor_commShift ObjectProperty.commShiftι
set_option backward.isDefEq.respectTransparency true

private theorem localized_inverse_commShift
    {K D E : Type*} [Category K] [Category D] [Category E]
    [HasShift K ℤ] [HasShift D ℤ] [Preadditive E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : K ⥤ D) [L.CommShift ℤ] (W : MorphismProperty K)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : K ⥤ K ⥤ E) [F.CommShift₂Int] (G : D ⥤ D ⥤ E)
    [Localization.Lifting₂ L L W W F G] (X : K) :
    let := Functor.commShift₂OfLocalization L L W W F G .int
    let e : L ⋙ G.obj (L.obj X) ≅ F.obj X :=
      (Localization.Lifting₂.iso L L W W F G).app X
    NatTrans.CommShift e.inv ℤ := by
  let := Functor.commShift₂OfLocalization L L W W F G .int
  let e : L ⋙ G.obj (L.obj X) ≅ F.obj X :=
    (Localization.Lifting₂.iso L L W W F G).app X
  have : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L W W F G X
  exact NatTrans.CommShift.of_iso_inv e ℤ

private theorem localized_flip_inverse_commShift
    {K D E : Type*} [Category K] [Category D] [Category E]
    [HasShift K ℤ] [HasShift D ℤ] [Preadditive E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : K ⥤ D) [L.CommShift ℤ] (W : MorphismProperty K)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : K ⥤ K ⥤ E) [F.CommShift₂Int] (G : D ⥤ D ⥤ E)
    [Localization.Lifting₂ L L W W F G] (X : K) :
    let := Functor.commShift₂OfLocalization L L W W F G .int
    let := Localization.Lifting₂.flip L L W W F G
    let e : L ⋙ G.flip.obj (L.obj X) ≅ F.flip.obj X :=
      (Localization.Lifting₂.iso L L W W F.flip G.flip).app X
    NatTrans.CommShift e.inv ℤ := by
  let := Functor.commShift₂OfLocalization L L W W F G .int
  let := Localization.Lifting₂.flip L L W W F G
  let e : L ⋙ G.flip.obj (L.obj X) ≅ F.flip.obj X :=
    (Localization.Lifting₂.iso L L W W F.flip G.flip).app X
  have : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L W W F.flip G.flip X
  exact NatTrans.CommShift.of_iso_inv e ℤ

private theorem quotientPredicate_shift
    {A : Type*} [Category A] [Preadditive A]
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)))
    (Q : CochainComplex A ℤ → Prop)
    (hP : ∀ X, P X ↔ Q X.as)
    (stable : ∀ K, Q K → ∀ n : ℤ, Q (K⟦n⟧))
    (n : ℤ) (X : HomotopyCategory A (ComplexShape.up ℤ)) (hX : P X) :
    P (X⟦n⟧) := by
  obtain ⟨K, rfl⟩ := X.quotient_obj_surjective
  rw [HomotopyCategory.shift_quotient_obj]
  exact (hP _).2 (stable K ((hP _).1 hX) n)

private theorem quotientPredicateStable
    {A : Type*} [Category A] [Preadditive A]
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)))
    (Q : CochainComplex A ℤ → Prop)
    (hP : ∀ X, P X ↔ Q X.as)
    (stable : ∀ K, Q K → ∀ n : ℤ, Q (K⟦n⟧)) : P.IsStableUnderShift ℤ :=
  { isStableUnderShiftBy n := ⟨fun X hX ↦ quotientPredicate_shift P Q hP stable n X hX⟩ }

private theorem quotient_shift_hom
    {A : Type*} [Category A] [Preadditive A] (P : CochainComplex A ℤ) (n : ℤ) :
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).hom.app P = 𝟙 _ := by
  rfl

private theorem inclusion_shift_hom
    {A : Type*} [Category A] [HasShift A ℤ] (P : ObjectProperty A)
    [P.IsStableUnderShift ℤ] (X : P.FullSubcategory) (n : ℤ) :
    (P.ι.commShiftIso n).hom.app X = 𝟙 _ := by
  rfl

private theorem Q_shift_hom
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.Q.commShiftIso n).hom.app P =
      (DerivedCategory.Qh.commShiftIso n).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) := by
  have hh := NatTrans.shift_app_comm (DerivedCategory.quotientCompQhIso A).hom n P
  simp only [Functor.commShiftIso_comp_hom_app, quotientCompQh_hom,
    quotient_shift_hom] at hh
  dsimp only [Functor.comp_obj] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.id_comp] at hh
  exact hh.symm

private def curryPostcompIso
    {C₁ C₂ D E : Type*} [Category C₁] [Category C₂] [Category D] [Category E]
    (F : C₁ × C₂ ⥤ D) (Q : D ⥤ E) :
    curry.obj (F ⋙ Q) ≅ curry.obj F ⋙ (whiskeringRight _ _ _).obj Q :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _))

private def curryUncurryIso
    {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    (F : C₁ ⥤ C₂ ⥤ D) : curry.obj (uncurry.obj F) ≅ F :=
  (currying.unitIso.app F).symm

@[irreducible]
private def complexLiftingIso
    {K D : Type*} [Category K] [Category D]
    (q : K ⥤ D) (B : D × D ⥤ D) (T : K ⥤ K ⥤ K)
    (c : q.prod q ⋙ B ≅ uncurry.obj T ⋙ q) :
    q ⋙ curry.obj B ⋙ (whiskeringLeft _ _ _).obj q ≅
      T ⋙ (whiskeringRight _ _ _).obj q :=
  (curryObjProdComp q q B).symm ≪≫ curry.mapIso c ≪≫
    curryPostcompIso _ q ≪≫ isoWhiskerRight (curryUncurryIso T) _

private theorem complexLiftingIso_inv
    {K D : Type*} [Category K] [Category D]
    (q : K ⥤ D) (B : D × D ⥤ D) (T : K ⥤ K ⥤ K)
    (c : q.prod q ⋙ B ≅ uncurry.obj T ⋙ q) (X Y : K) :
    ((complexLiftingIso q B T c).inv.app X).app Y = c.inv.app (X, Y) := by
  simp [complexLiftingIso, curryPostcompIso, curryUncurryIso, curryObjProdComp]

@[irreducible]
private def derivedLiftingIso
    {K D E : Type*} [Category K] [Category D] [Category E]
    (i : K ⥤ D) (q : D ⥤ E) (B : D × D ⥤ D) (U : E × E ⥤ E)
    (d : i.prod i ⋙ B ⋙ q ≅ (i ⋙ q).prod (i ⋙ q) ⋙ U) :
    (i ⋙ q) ⋙ curry.obj U ⋙ (whiskeringLeft _ _ _).obj (i ⋙ q) ≅
      (i ⋙ curry.obj B ⋙ (whiskeringLeft _ _ _).obj i) ⋙
        (whiskeringRight _ _ _).obj q :=
  (curryObjProdComp (i ⋙ q) (i ⋙ q) U).symm ≪≫ curry.mapIso d.symm ≪≫
    curry.mapIso (Functor.associator (i.prod i) B q).symm ≪≫
    curryPostcompIso _ q ≪≫ isoWhiskerRight (curryObjProdComp i i B) _

private theorem derivedLiftingIso_inv
    {K D E : Type*} [Category K] [Category D] [Category E]
    (i : K ⥤ D) (q : D ⥤ E) (B : D × D ⥤ D) (U : E × E ⥤ E)
    (d : i.prod i ⋙ B ⋙ q ≅ (i ⋙ q).prod (i ⋙ q) ⋙ U) (X Y : K) :
    ((derivedLiftingIso i q B U d).inv.app X).app Y = d.hom.app (X, Y) := by
  simp [derivedLiftingIso, curryPostcompIso, curryObjProdComp]

private theorem complexLiftingIso_flip_inv
    {K D : Type*} [Category K] [Category D]
    (q : K ⥤ D) (B : D × D ⥤ D) (T : K ⥤ K ⥤ K)
    (c : q.prod q ⋙ B ≅ uncurry.obj T ⋙ q) (X Y : K) :
    ((((flipFunctor _ _ _).mapIso (complexLiftingIso q B T c)).inv.app Y).app X) =
      c.inv.app (X, Y) := complexLiftingIso_inv q B T c X Y

private theorem derivedLiftingIso_flip_inv
    {K D E : Type*} [Category K] [Category D] [Category E]
    (i : K ⥤ D) (q : D ⥤ E) (B : D × D ⥤ D) (U : E × E ⥤ E)
    (d : i.prod i ⋙ B ⋙ q ≅ (i ⋙ q).prod (i ⋙ q) ⋙ U) (X Y : K) :
    ((((flipFunctor _ _ _).mapIso (derivedLiftingIso i q B U d)).inv.app Y).app X) =
      d.hom.app (X, Y) := derivedLiftingIso_inv i q B U d X Y

section QuotientSquares

variable {A : Type*} [Category A] [Preadditive A]

local notation "K₀" => CochainComplex A ℤ
local notation "H₀" => HomotopyCategory A (ComplexShape.up ℤ)
local notation "q₀" => HomotopyCategory.quotient A (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientLifting_shift_square
    (B : H₀ × H₀ ⥤ H₀) (T : K₀ ⥤ K₀ ⥤ K₀)
    [(curry.obj B).CommShift₂Int] [∀ X, (T.obj X).CommShift ℤ]
    (c : (q₀).prod q₀ ⋙ B ≅ uncurry.obj T ⋙ q₀)
    (X Y : K₀) (n : ℤ)
    (h : let e : q₀ ⋙ (curry.obj B).obj ((q₀).obj X) ≅ T.obj X ⋙ q₀ :=
      (complexLiftingIso q₀ B T c).app X
      NatTrans.CommShift e.inv ℤ) :
    (q₀).map (((T.obj X).commShiftIso n).hom.app Y) ≫ (c.inv.app (X, Y))⟦n⟧' =
      c.inv.app (X, Y⟦n⟧) ≫
        (((curry.obj B).obj ((q₀).obj X)).commShiftIso n).hom.app ((q₀).obj Y) := by
  let e : q₀ ⋙ (curry.obj B).obj ((q₀).obj X) ≅ T.obj X ⋙ q₀ :=
    (complexLiftingIso q₀ B T c).app X
  have : NatTrans.CommShift e.inv ℤ := h
  have hh := NatTrans.shift_app_comm e.inv n Y
  change ((T.obj X ⋙ q₀).commShiftIso n).hom.app Y ≫
      (e.inv.app Y)⟦n⟧' = e.inv.app (Y⟦n⟧) ≫
      ((q₀ ⋙ (curry.obj B).obj ((q₀).obj X)).commShiftIso n).hom.app Y at hh
  simp only [e, Iso.app_inv, complexLiftingIso_inv,
    Functor.commShiftIso_comp_hom_app, quotient_shift_hom] at hh
  dsimp only [Functor.comp_obj, Functor.curry_obj_obj_obj, Functor.flip_obj_obj,
    Functor.prod_obj] at hh ⊢
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientLifting_flip_shift_square
    (B : H₀ × H₀ ⥤ H₀) (T : K₀ ⥤ K₀ ⥤ K₀)
    [(curry.obj B).CommShift₂Int] [∀ X, (T.flip.obj X).CommShift ℤ]
    (c : (q₀).prod q₀ ⋙ B ≅ uncurry.obj T ⋙ q₀)
    (X Y : K₀) (n : ℤ)
    (h : let e : q₀ ⋙ (curry.obj B).flip.obj ((q₀).obj Y) ≅ T.flip.obj Y ⋙ q₀ :=
      ((flipFunctor _ _ _).mapIso (complexLiftingIso q₀ B T c)).app Y
      NatTrans.CommShift e.inv ℤ) :
    (q₀).map (((T.flip.obj Y).commShiftIso n).hom.app X) ≫ (c.inv.app (X, Y))⟦n⟧' =
      c.inv.app (X⟦n⟧, Y) ≫
        (((curry.obj B).flip.obj ((q₀).obj Y)).commShiftIso n).hom.app ((q₀).obj X) := by
  let e : q₀ ⋙ (curry.obj B).flip.obj ((q₀).obj Y) ≅ T.flip.obj Y ⋙ q₀ :=
    ((flipFunctor _ _ _).mapIso (complexLiftingIso q₀ B T c)).app Y
  have : NatTrans.CommShift e.inv ℤ := h
  have hh := NatTrans.shift_app_comm e.inv n X
  change ((T.flip.obj Y ⋙ q₀).commShiftIso n).hom.app X ≫
      (e.inv.app X)⟦n⟧' = e.inv.app (X⟦n⟧) ≫
      ((q₀ ⋙ (curry.obj B).flip.obj ((q₀).obj Y)).commShiftIso n).hom.app X at hh
  simp only [e, Iso.app_inv, complexLiftingIso_flip_inv,
    Functor.commShiftIso_comp_hom_app, quotient_shift_hom] at hh
  dsimp only [Functor.comp_obj, Functor.curry_obj_obj_obj, Functor.flip_obj_obj,
    Functor.prod_obj] at hh ⊢
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Category.assoc] using hh

end QuotientSquares

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem subcategoryLifting_shift_square
    {D E : Type*} [Category D] [Category E] [Preadditive D] [Preadditive E]
    [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (q : D ⥤ E) [q.CommShift ℤ] (B : D × D ⥤ D) (U : E × E ⥤ E)
    [(curry.obj B).CommShift₂Int] [(curry.obj U).CommShift₂Int]
    (d : P.ι.prod P.ι ⋙ B ⋙ q ≅ (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ U)
    (X Y : P.FullSubcategory) (n : ℤ)
    (h : let e : (P.ι ⋙ q) ⋙ (curry.obj U).obj ((P.ι ⋙ q).obj X) ≅
        (P.ι ⋙ (curry.obj B).obj X.obj) ⋙ q :=
      (derivedLiftingIso P.ι q B U d).app X
      NatTrans.CommShift e.inv ℤ) :
    q.map ((((curry.obj B).obj X.obj).commShiftIso n).hom.app Y.obj) ≫
        (q.commShiftIso n).hom.app (B.obj (X.obj, Y.obj)) ≫
        (d.hom.app (X, Y))⟦n⟧' =
      d.hom.app (X, Y⟦n⟧) ≫
        ((curry.obj U).obj (q.obj X.obj)).map ((q.commShiftIso n).hom.app Y.obj) ≫
        (((curry.obj U).obj (q.obj X.obj)).commShiftIso n).hom.app (q.obj Y.obj) := by
  let e : (P.ι ⋙ q) ⋙ (curry.obj U).obj ((P.ι ⋙ q).obj X) ≅
      (P.ι ⋙ (curry.obj B).obj X.obj) ⋙ q :=
    (derivedLiftingIso P.ι q B U d).app X
  have : NatTrans.CommShift e.inv ℤ := h
  have hh := NatTrans.shift_app_comm e.inv n Y
  change (((P.ι ⋙ (curry.obj B).obj X.obj) ⋙ q).commShiftIso n).hom.app Y ≫
      (e.inv.app Y)⟦n⟧' = e.inv.app (Y⟦n⟧) ≫
      (((P.ι ⋙ q) ⋙ (curry.obj U).obj ((P.ι ⋙ q).obj X)).commShiftIso n).hom.app Y at hh
  simp only [e, Iso.app_inv, derivedLiftingIso_inv,
    Functor.commShiftIso_comp_hom_app, inclusion_shift_hom] at hh
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.curry_obj_obj_obj,
    Functor.flip_obj_obj, Functor.prod_obj] at hh ⊢
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem subcategoryLifting_flip_shift_square
    {D E : Type*} [Category D] [Category E] [Preadditive D] [Preadditive E]
    [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (q : D ⥤ E) [q.CommShift ℤ] (B : D × D ⥤ D) (U : E × E ⥤ E)
    [(curry.obj B).CommShift₂Int] [(curry.obj U).CommShift₂Int]
    (d : P.ι.prod P.ι ⋙ B ⋙ q ≅ (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ U)
    (X Y : P.FullSubcategory) (n : ℤ)
    (h : let e : (P.ι ⋙ q) ⋙ (curry.obj U).flip.obj ((P.ι ⋙ q).obj Y) ≅
        (P.ι ⋙ (curry.obj B).flip.obj Y.obj) ⋙ q :=
      ((flipFunctor _ _ _).mapIso (derivedLiftingIso P.ι q B U d)).app Y
      NatTrans.CommShift e.inv ℤ) :
    q.map ((((curry.obj B).flip.obj Y.obj).commShiftIso n).hom.app X.obj) ≫
        (q.commShiftIso n).hom.app (B.obj (X.obj, Y.obj)) ≫
        (d.hom.app (X, Y))⟦n⟧' =
      d.hom.app (X⟦n⟧, Y) ≫
        ((curry.obj U).flip.obj (q.obj Y.obj)).map ((q.commShiftIso n).hom.app X.obj) ≫
        (((curry.obj U).flip.obj (q.obj Y.obj)).commShiftIso n).hom.app (q.obj X.obj) := by
  let e : (P.ι ⋙ q) ⋙ (curry.obj U).flip.obj ((P.ι ⋙ q).obj Y) ≅
      (P.ι ⋙ (curry.obj B).flip.obj Y.obj) ⋙ q :=
    ((flipFunctor _ _ _).mapIso (derivedLiftingIso P.ι q B U d)).app Y
  have : NatTrans.CommShift e.inv ℤ := h
  have hh := NatTrans.shift_app_comm e.inv n X
  change (((P.ι ⋙ (curry.obj B).flip.obj Y.obj) ⋙ q).commShiftIso n).hom.app X ≫
      (e.inv.app X)⟦n⟧' = e.inv.app (X⟦n⟧) ≫
      (((P.ι ⋙ q) ⋙ (curry.obj U).flip.obj ((P.ι ⋙ q).obj Y)).commShiftIso n).hom.app X at hh
  simp only [e, Iso.app_inv, derivedLiftingIso_flip_inv,
    Functor.commShiftIso_comp_hom_app, inclusion_shift_hom] at hh
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.curry_obj_obj_obj,
    Functor.flip_obj_obj, Functor.prod_obj] at hh ⊢
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Category.assoc] using hh

private theorem quotientTensorShifts
    {A : Type*} [Category A] [Preadditive A] [Limits.HasBinaryBiproducts A]
    (B : HomotopyCategory A (ComplexShape.up ℤ) ×
      HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory A (ComplexShape.up ℤ))
    (T : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    [T.CommShift₂Int]
    (c : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).prod
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙ B ≅
      uncurry.obj T ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ)) :
    ∃ s : (curry.obj B).CommShift₂Int, let := s
      ∀ (X Y : CochainComplex A ℤ) (n : ℤ),
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (((T.flip.obj Y).commShiftIso n).hom.app X) ≫ (c.inv.app (X, Y))⟦n⟧' =
          c.inv.app (X⟦n⟧, Y) ≫
            (((curry.obj B).flip.obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)).commShiftIso n).hom.app
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X)) ∧
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (((T.obj X).commShiftIso n).hom.app Y) ≫ (c.inv.app (X, Y))⟦n⟧' =
          c.inv.app (X, Y⟦n⟧) ≫
            (((curry.obj B).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X)).commShiftIso n).hom.app
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y)) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let W := HomologicalComplex.homotopyEquivalences A (.up ℤ)
  let H := curry.obj B
  let F := T ⋙ (whiskeringRight _ _ _).obj q
  let : F.CommShift₂Int := Functor.CommShift₂.postcompInt T q
  let : Localization.Lifting₂ q q W W F H := ⟨complexLiftingIso q B T c⟩
  let s : H.CommShift₂Int := Functor.commShift₂OfLocalization q q W W F H .int
  refine ⟨s, ?_⟩
  let := s
  dsimp only
  intro X Y n
  constructor
  · exact quotientLifting_flip_shift_square B T c X Y n
      (localized_flip_inverse_commShift q W F H Y)
  · exact quotientLifting_shift_square B T c X Y n
      (localized_inverse_commShift q W F H X)

private theorem resolvingTensorShifts
    {D E : Type*} [Category D] [Category E] [Preadditive D] [Preadditive E]
    [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (P : ObjectProperty D) [P.IsStableUnderShift ℤ]
    (q : D ⥤ E) [q.CommShift ℤ] [q.Additive]
    (W : MorphismProperty P.FullSubcategory) [(P.ι ⋙ q).IsLocalization W]
    [W.ContainsIdentities]
    (B : D × D ⥤ D) [(curry.obj B).CommShift₂Int] (U : E × E ⥤ E)
    (d : P.ι.prod P.ι ⋙ B ⋙ q ≅ (P.ι ⋙ q).prod (P.ι ⋙ q) ⋙ U) :
    ∃ s : (curry.obj U).CommShift₂Int, let := s
      ∀ (X Y : P.FullSubcategory) (n : ℤ),
        (q.map ((((curry.obj B).flip.obj Y.obj).commShiftIso n).hom.app X.obj) ≫
            (q.commShiftIso n).hom.app (B.obj (X.obj, Y.obj)) ≫
            (d.hom.app (X, Y))⟦n⟧' =
          d.hom.app (X⟦n⟧, Y) ≫
            ((curry.obj U).flip.obj (q.obj Y.obj)).map
              ((q.commShiftIso n).hom.app X.obj) ≫
            (((curry.obj U).flip.obj (q.obj Y.obj)).commShiftIso n).hom.app (q.obj X.obj)) ∧
        (q.map ((((curry.obj B).obj X.obj).commShiftIso n).hom.app Y.obj) ≫
            (q.commShiftIso n).hom.app (B.obj (X.obj, Y.obj)) ≫
            (d.hom.app (X, Y))⟦n⟧' =
          d.hom.app (X, Y⟦n⟧) ≫
            ((curry.obj U).obj (q.obj X.obj)).map ((q.commShiftIso n).hom.app Y.obj) ≫
            (((curry.obj U).obj (q.obj X.obj)).commShiftIso n).hom.app (q.obj Y.obj)) := by
  let H := curry.obj B
  let L := P.ι ⋙ q
  let H₂ := H ⋙ (whiskeringLeft _ _ _).obj P.ι
  let : H₂.CommShift₂Int := Functor.CommShift₂.precomp₂ P.ι H .int
  let Hres := P.ι ⋙ H₂
  let : Hres.CommShift₂Int := Functor.CommShift₂.precomp₁ P.ι H₂ .int
  let F := Hres ⋙ (whiskeringRight _ _ _).obj q
  let : F.CommShift₂Int := Functor.CommShift₂.postcompInt Hres q
  let T := curry.obj U
  let : Localization.Lifting₂ L L W W F T := ⟨derivedLiftingIso P.ι q B U d⟩
  let s : T.CommShift₂Int := Functor.commShift₂OfLocalization L L W W F T .int
  refine ⟨s, ?_⟩
  let := s
  dsimp only
  intro X Y n
  constructor
  · exact subcategoryLifting_flip_shift_square P q B U d X Y n
      (localized_flip_inverse_commShift L W F T Y)
  · exact subcategoryLifting_shift_square P q B U d X Y n
      (localized_inverse_commShift L W F T X)

private theorem paste_shift_squares
    {K D : Type*} [Category K] [Category D] [HasShift K ℤ] [HasShift D ℤ]
    (q : K ⥤ D) [q.CommShift ℤ] (n : ℤ)
    {X X' Y Y' : K} {Z Z' : D}
    (a : X' ⟶ X⟦n⟧) (c : X ⟶ Y) (c' : X' ⟶ Y') (h : Y' ⟶ Y⟦n⟧)
    (d : q.obj Y ⟶ Z) (d' : q.obj Y' ⟶ Z') (k : Z' ⟶ Z⟦n⟧)
    (hc : a ≫ c⟦n⟧' = c' ≫ h)
    (hd : q.map h ≫ (q.commShiftIso n).hom.app Y ≫ d⟦n⟧' = d' ≫ k) :
    (q.map c' ≫ d') ≫ k =
      q.map a ≫ (q.commShiftIso n).hom.app X ≫ (q.map c ≫ d)⟦n⟧' := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← hd, ← CategoryTheory.Functor.map_comp_assoc, ← hc,
    CategoryTheory.Functor.map_comp, Category.assoc,
    q.commShiftIso_hom_naturality_assoc]

private def representativePair
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (P : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (Q : CochainComplex A ℤ → Prop) (hP : ∀ X, P X ↔ Q X.as)
    (B : HomotopyCategory A (.up ℤ) × HomotopyCategory A (.up ℤ) ⥤
      HomotopyCategory A (.up ℤ))
    (U : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (c : (HomotopyCategory.quotient A (.up ℤ)).prod
      (HomotopyCategory.quotient A (.up ℤ)) ⋙ B ≅
      uncurry.obj F ⋙ HomotopyCategory.quotient A (.up ℤ))
    (d : P.ι.prod P.ι ⋙ B ⋙ DerivedCategory.Qh ≅
      (P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh) ⋙ U)
    (X Y : CochainComplex A ℤ) (hX : Q X) (hY : Q Y) :
    DerivedCategory.Q.obj ((F.obj X).obj Y) ≅
      U.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) :=
  (DerivedCategory.quotientCompQhIso A).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (c.symm.app (X, Y)) ≪≫
    d.app (⟨(HomotopyCategory.quotient A (.up ℤ)).obj X, (hP _).2 hX⟩,
      ⟨(HomotopyCategory.quotient A (.up ℤ)).obj Y, (hP _).2 hY⟩) ≪≫
    U.mapIso (Iso.prod ((DerivedCategory.quotientCompQhIso A).app X)
      ((DerivedCategory.quotientCompQhIso A).app Y))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem representativePair_hom
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (P : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (Q : CochainComplex A ℤ → Prop) (hP : ∀ X, P X ↔ Q X.as)
    (B : HomotopyCategory A (.up ℤ) × HomotopyCategory A (.up ℤ) ⥤
      HomotopyCategory A (.up ℤ))
    (U : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (c : (HomotopyCategory.quotient A (.up ℤ)).prod
      (HomotopyCategory.quotient A (.up ℤ)) ⋙ B ≅
      uncurry.obj F ⋙ HomotopyCategory.quotient A (.up ℤ))
    (d : P.ι.prod P.ι ⋙ B ⋙ DerivedCategory.Qh ≅
      (P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh) ⋙ U)
    (X Y : CochainComplex A ℤ) (hX : Q X) (hY : Q Y) :
    (representativePair F P Q hP B U c d X Y hX hY).hom =
      DerivedCategory.Qh.map (c.inv.app (X, Y)) ≫
      d.hom.app (⟨(HomotopyCategory.quotient A (.up ℤ)).obj X, (hP _).2 hX⟩,
        ⟨(HomotopyCategory.quotient A (.up ℤ)).obj Y, (hP _).2 hY⟩) := by
  simp only [representativePair, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, quotientCompQh_hom, quotientCompQh_inv, Iso.prod_hom,
    ← CategoryTheory.prod_id, Category.id_comp]
  erw [U.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorShifts_normalized
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    [F.CommShift₂Int]
    (P : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (Q : CochainComplex A ℤ → Prop) (hPmem : ∀ X, P X ↔ Q X.as)
    (stable : ∀ X, Q X → ∀ n : ℤ, Q (X⟦n⟧))
    (B : HomotopyCategory A (.up ℤ) × HomotopyCategory A (.up ℤ) ⥤
      HomotopyCategory A (.up ℤ))
    (U : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (c : (HomotopyCategory.quotient A (.up ℤ)).prod
      (HomotopyCategory.quotient A (.up ℤ)) ⋙ B ≅
      uncurry.obj F ⋙ HomotopyCategory.quotient A (.up ℤ))
    (d : P.ι.prod P.ι ⋙ B ⋙ DerivedCategory.Qh ≅
      (P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh) ⋙ U)
    [(P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι)]
    (pair : ∀ (X Y : CochainComplex A ℤ) (_ : Q X) (_ : Q Y),
      DerivedCategory.Q.obj ((F.obj X).obj Y) ≅
        U.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y))
    (hp : ∀ (X Y : CochainComplex A ℤ) (hX : Q X) (hY : Q Y),
      (pair X Y hX hY).hom = DerivedCategory.Qh.map (c.inv.app (X, Y)) ≫
        d.hom.app (⟨(HomotopyCategory.quotient A (.up ℤ)).obj X, (hPmem _).2 hX⟩,
          ⟨(HomotopyCategory.quotient A (.up ℤ)).obj Y, (hPmem _).2 hY⟩)) :
    ∃ s : (curry.obj U).CommShift₂Int, let := s
      ∀ (X Y : CochainComplex A ℤ) (hX : Q X) (hY : Q Y) (n : ℤ),
        ((pair (X⟦n⟧) Y (stable X hX n) hY).hom ≫
            ((curry.obj U).flip.obj (DerivedCategory.Q.obj Y)).map
              ((DerivedCategory.Q.commShiftIso n).hom.app X) ≫
            (((curry.obj U).flip.obj (DerivedCategory.Q.obj Y)).commShiftIso n).hom.app
              (DerivedCategory.Q.obj X) =
          DerivedCategory.Q.map (((F.flip.obj Y).commShiftIso n).hom.app X) ≫
            (DerivedCategory.Q.commShiftIso n).hom.app ((F.obj X).obj Y) ≫
            (pair X Y hX hY).hom⟦n⟧') ∧
        ((pair X (Y⟦n⟧) hX (stable Y hY n)).hom ≫
            ((curry.obj U).obj (DerivedCategory.Q.obj X)).map
              ((DerivedCategory.Q.commShiftIso n).hom.app Y) ≫
            (((curry.obj U).obj (DerivedCategory.Q.obj X)).commShiftIso n).hom.app
              (DerivedCategory.Q.obj Y) =
          DerivedCategory.Q.map (((F.obj X).commShiftIso n).hom.app Y) ≫
            (DerivedCategory.Q.commShiftIso n).hom.app ((F.obj X).obj Y) ≫
            (pair X Y hX hY).hom⟦n⟧') := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let qh := DerivedCategory.Qh (C := A)
  let H := curry.obj B
  let T := curry.obj U
  obtain ⟨sH, hcomplex⟩ := quotientTensorShifts B F c
  let : H.CommShift₂Int := sH
  let : P.IsStableUnderShift ℤ := quotientPredicateStable P Q hPmem stable
  let W := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  obtain ⟨s, hderived⟩ := resolvingTensorShifts P qh W B U d
  refine ⟨s, ?_⟩
  let := s
  dsimp only
  intro P₀ S₀ hP₀ hS₀ n
  let p : P.FullSubcategory := ⟨q.obj P₀, (hPmem _).2 hP₀⟩
  let t : P.FullSubcategory := ⟨q.obj S₀, (hPmem _).2 hS₀⟩
  constructor
  · have hc := (hcomplex P₀ S₀ n).1
    have hd := (hderived p t n).1
    let c₀ := c.symm.app (P₀, S₀)
    let c₁ := c.symm.app (P₀⟦n⟧, S₀)
    let d₀ := d.app (p, t)
    let p₁ : P.FullSubcategory := ⟨q.obj (P₀⟦n⟧), (hPmem _).2 (stable P₀ hP₀ n)⟩
    let d₁ := d.app (p₁, t)
    let a := ((F.flip.obj S₀).commShiftIso n).hom.app P₀
    have hc' : q.map a ≫ c₀.hom⟦n⟧' = c₁.hom ≫
        ((H.flip.obj (q.obj S₀)).commShiftIso n).hom.app (q.obj P₀) := hc
    have hd' : qh.map
        (((H.flip.obj (q.obj S₀)).commShiftIso n).hom.app (q.obj P₀)) ≫
        (qh.commShiftIso n).hom.app (B.obj (q.obj P₀, q.obj S₀)) ≫
        d₀.hom⟦n⟧' = d₁.hom ≫
        (T.flip.obj (DerivedCategory.Q.obj S₀)).map
          ((qh.commShiftIso n).hom.app (q.obj P₀)) ≫
        ((T.flip.obj (DerivedCategory.Q.obj S₀)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P₀) := hd
    have hh := paste_shift_squares qh n (q.map a) c₀.hom c₁.hom
      (((H.flip.obj (q.obj S₀)).commShiftIso n).hom.app (q.obj P₀)) d₀.hom d₁.hom
      ((T.flip.obj (DerivedCategory.Q.obj S₀)).map
          ((qh.commShiftIso n).hom.app (q.obj P₀)) ≫
        ((T.flip.obj (DerivedCategory.Q.obj S₀)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P₀)) hc' hd'
    rw [hp, hp, Q_shift_hom, Q_shift_hom, Q_map a]
    simp only [c₀, c₁, d₀, d₁, p, t, p₁, q, qh, T,
      Iso.symm_hom, Iso.app_hom, Category.assoc] at hh
    convert! hh using 1
    simp only [Category.assoc]
  · have hc := (hcomplex P₀ S₀ n).2
    have hd := (hderived p t n).2
    let c₀ := c.symm.app (P₀, S₀)
    let c₁ := c.symm.app (P₀, S₀⟦n⟧)
    let d₀ := d.app (p, t)
    let t₁ : P.FullSubcategory := ⟨q.obj (S₀⟦n⟧), (hPmem _).2 (stable S₀ hS₀ n)⟩
    let d₁ := d.app (p, t₁)
    let a := ((F.obj P₀).commShiftIso n).hom.app S₀
    have hc' : q.map a ≫ c₀.hom⟦n⟧' = c₁.hom ≫
        ((H.obj (q.obj P₀)).commShiftIso n).hom.app (q.obj S₀) := hc
    have hd' : qh.map
        (((H.obj (q.obj P₀)).commShiftIso n).hom.app (q.obj S₀)) ≫
        (qh.commShiftIso n).hom.app (B.obj (q.obj P₀, q.obj S₀)) ≫
        d₀.hom⟦n⟧' = d₁.hom ≫
        (T.obj (DerivedCategory.Q.obj P₀)).map
          ((qh.commShiftIso n).hom.app (q.obj S₀)) ≫
        ((T.obj (DerivedCategory.Q.obj P₀)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj S₀) := hd
    have hh := paste_shift_squares qh n (q.map a) c₀.hom c₁.hom
      (((H.obj (q.obj P₀)).commShiftIso n).hom.app (q.obj S₀)) d₀.hom d₁.hom
      ((T.obj (DerivedCategory.Q.obj P₀)).map
          ((qh.commShiftIso n).hom.app (q.obj S₀)) ≫
        ((T.obj (DerivedCategory.Q.obj P₀)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj S₀)) hc' hd'
    rw [hp, hp, Q_shift_hom, Q_shift_hom, Q_map a]
    simp only [c₀, c₁, d₀, d₁, p, t, t₁, q, qh, T,
      Iso.symm_hom, Iso.app_hom, Category.assoc] at hh
    convert! hh using 1
    simp only [Category.assoc]

private def firstShiftIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (shiftFunctor D n).prod (𝟭 D) ⋙ uncurry.obj T ≅
      uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.flip.obj X.2).commShiftIso n).app X.1) (by
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
    change ((T.map (f₁⟦n⟧')).app X₂ ≫ (T.obj (Y₁⟦n⟧)).map f₂) ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
    have hh := NatTrans.shift_app_comm (T.flip.map f₂) n Y₁
    change ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ ≫
      ((T.obj Y₁).map f₂)⟦n⟧' = (T.obj (Y₁⟦n⟧)).map f₂ ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ at hh
    have h₁ := (T.flip.obj X₂).commShiftIso_hom_naturality f₁ n
    change (T.map (f₁⟦n⟧')).app X₂ ≫
        ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂)⟦n⟧' at h₁
    rw [Category.assoc, ← hh, ← Category.assoc, h₁, Category.assoc,
      CategoryTheory.Functor.map_comp])

private def secondShiftIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (𝟭 D).prod (shiftFunctor D n) ⋙ uncurry.obj T ≅
      uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.obj X.1).commShiftIso n).app X.2) (by
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
    change ((T.map f₁).app (X₂⟦n⟧) ≫ (T.obj Y₁).map (f₂⟦n⟧')) ≫
        ((T.obj Y₁).commShiftIso n).hom.app Y₂ =
      ((T.obj X₁).commShiftIso n).hom.app X₂ ≫
        ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
    rw [Category.assoc, (T.obj Y₁).commShiftIso_hom_naturality f₂ n, ← Category.assoc,
      ← NatTrans.shift_app_comm (T.map f₁), Category.assoc, CategoryTheory.Functor.map_comp])

private theorem natTrans_prod_ext_of_representatives
    {K D E : Type*} [Category D] [Category E]
    (L : K → D) (P : K → Prop)
    (repr : ∀ M : D, ∃ X, P X ∧ Nonempty (L X ≅ M))
    {F G : D × D ⥤ E} (α β : F ⟶ G)
    (h : ∀ X Y, P X → P Y → α.app (L X, L Y) = β.app (L X, L Y)) : α = β := by
  ext ⟨M, N⟩
  obtain ⟨X, hX, ⟨eX⟩⟩ := repr M
  obtain ⟨Y, hY, ⟨eY⟩⟩ := repr N
  let e := eX.prod eY
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality e.hom, β.naturality e.hom, h X Y hX hY]

private theorem shift_unique_generic
    {D K : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (U : D × D ⥤ D) [(curry.obj U).CommShift₂Int]
    (L : K → D) (P : K → Prop)
    (repr : ∀ M : D, ∃ X, P X ∧ Nonempty (L X ≅ M)) :
    (∀ (n : ℤ) (α : (shiftFunctor D n).prod (𝟭 D) ⋙ U ≅ U ⋙ shiftFunctor D n),
      (∀ X Y, P X → P Y → α.hom.app (L X, L Y) =
        (((curry.obj U).flip.obj (L Y)).commShiftIso n).hom.app (L X)) →
      ∀ M N, α.hom.app (M, N) =
        (((curry.obj U).flip.obj N).commShiftIso n).hom.app M) ∧
    (∀ (n : ℤ) (α : (𝟭 D).prod (shiftFunctor D n) ⋙ U ≅ U ⋙ shiftFunctor D n),
      (∀ X Y, P X → P Y → α.hom.app (L X, L Y) =
        (((curry.obj U).obj (L X)).commShiftIso n).hom.app (L Y)) →
      ∀ M N, α.hom.app (M, N) =
        (((curry.obj U).obj M).commShiftIso n).hom.app N) := by
  let T := curry.obj U
  constructor
  · intro n α h M N
    let β := isoWhiskerLeft ((shiftFunctor _ n).prod (𝟭 _))
        (currying.counitIso.app U).symm ≪≫ firstShiftIso T n ≪≫
      isoWhiskerRight (currying.counitIso.app U) (shiftFunctor _ n)
    have hh := natTrans_prod_ext_of_representatives L
      P repr α.hom β.hom
      (by
        intro X Y hX hY
        dsimp only [β, firstShiftIso, secondShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
          whiskerLeft_app, whiskerRight_app, NatIso.ofComponents_hom_app,
          currying_counitIso_hom_app_app, currying_counitIso_inv_app_app]
        erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
        exact h X Y hX hY)
    have hh' := congr_app hh (M, N)
    dsimp only [β, firstShiftIso, secondShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
          whiskerLeft_app, whiskerRight_app, NatIso.ofComponents_hom_app,
          currying_counitIso_hom_app_app, currying_counitIso_inv_app_app] at hh'
    erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id] at hh'
    exact hh'
  · intro n α h M N
    let β := isoWhiskerLeft ((𝟭 _).prod (shiftFunctor _ n))
        (currying.counitIso.app U).symm ≪≫ secondShiftIso T n ≪≫
      isoWhiskerRight (currying.counitIso.app U) (shiftFunctor _ n)
    have hh := natTrans_prod_ext_of_representatives L
      P repr α.hom β.hom
      (by
        intro X Y hX hY
        dsimp only [β, firstShiftIso, secondShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
          whiskerLeft_app, whiskerRight_app, NatIso.ofComponents_hom_app,
          currying_counitIso_hom_app_app, currying_counitIso_inv_app_app]
        erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
        exact h X Y hX hY)
    have hh' := congr_app hh (M, N)
    dsimp only [β, firstShiftIso, secondShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
          whiskerLeft_app, whiskerRight_app, NatIso.ofComponents_hom_app,
          currying_counitIso_hom_app_app, currying_counitIso_inv_app_app] at hh'
    erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id] at hh'
    exact hh'

private theorem tensor_shift_unique
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int)
    (repr : ∀ M : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)),
      ∃ P, TensorFlatRepresentative (J := J) (R := R) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M)) :
    tensorShiftComparisonsUnique (J := J) (R := R) s := by
  let := s
  exact shift_unique_generic (siteDerivedTensorIndependentCoefficients J R)
    DerivedCategory.Q.obj (TensorFlatRepresentative (J := J) (R := R)) repr

private theorem commShift_of_resolving_components
    {K D : Type*} [Category K] [Category D] [HasShift K ℤ] [HasShift D ℤ]
    {H F : K ⥤ D} [H.CommShift ℤ] [F.CommShift ℤ]
    (e : H ≅ F) (P : ObjectProperty K)
    (res : ∀ (X : K) (n : ℤ), ∃ (Y : K) (f : Y ⟶ X),
      P Y ∧ IsIso (H.map (f⟦n⟧')))
    (onP : ∀ (Y : K), P Y → ∀ n : ℤ,
      (H.commShiftIso n).hom.app Y ≫ (e.hom.app Y)⟦n⟧' =
        e.hom.app (Y⟦n⟧) ≫ (F.commShiftIso n).hom.app Y) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro n
  ext X
  obtain ⟨Y, f, hY, hf⟩ := res X n
  let := hf
  apply (cancel_epi (H.map (f⟦n⟧'))).1
  dsimp
  rw [H.commShiftIso_hom_naturality_assoc]
  rw [← CategoryTheory.Functor.map_comp, e.hom.naturality, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, onP Y hY n]
  rw [Category.assoc, ← F.commShiftIso_hom_naturality,
    ← e.hom.naturality_assoc]

private theorem commShift_of_normalized_components
    {K D : Type*} [Category K] [Category D] [HasShift K ℤ] [HasShift D ℤ]
    {H F : K ⥤ D} [H.CommShift ℤ] [F.CommShift ℤ]
    (P : ObjectProperty K) (stable : ∀ X, P X → ∀ n : ℤ, P (X⟦n⟧))
    (c : ∀ X, P X → (H.obj X ≅ F.obj X))
    (res : ∀ (X : K) (n : ℤ), ∃ (Y : K) (f : Y ⟶ X),
      P Y ∧ IsIso (H.map (f⟦n⟧')))
    (hc : ∀ X hX n, (H.commShiftIso n).hom.app X ≫ (c X hX).hom⟦n⟧' =
      (c (X⟦n⟧) (stable X hX n)).hom ≫ (F.commShiftIso n).hom.app X)
    (e : H ≅ F) (norm : ∀ X hX, e.app X = c X hX) :
    NatTrans.CommShift e.hom ℤ := by
  apply commShift_of_resolving_components e P res
  intro X hX n
  rw [show e.hom.app X = (c X hX).hom from congrArg Iso.hom (norm X hX),
    show e.hom.app (X⟦n⟧) = (c (X⟦n⟧) (stable X hX n)).hom from
      congrArg Iso.hom (norm (X⟦n⟧) (stable X hX n))]
  exact hc X hX n

omit [HasDerivedCategory.{w} (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] in
private theorem flat_resolution
    (B : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    ∃ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (f : P ⟶ B), TensorFlatRepresentative (J := J) (R := R) P ∧ QuasiIso f := by
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients B
  refine ⟨P, f, ⟨hP, ?_⟩, hf⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hflat i)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_fixed_shift
    (stable : ∀ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧))
    (s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int)
    (hs : tensorResolvingShiftCompatible (J := J) (R := R) stable s) :
    tensorFixedComparisonsShiftCompatible (J := J) (R := R) s := by
  let := s
  intro A hA hmap
  constructor
  · intro eL norm
    apply commShift_of_normalized_components
      (H := (tensorShiftTotal (R := R)).obj A ⋙ DerivedCategory.Q)
      (F := DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (R := R)).obj
        (DerivedCategory.Q.obj A)) (TensorFlatRepresentative (J := J) (R := R))
      stable (fun B hB ↦ tensorDescentPair.{u, v, r, w} (J := J) (R := R) A B hA hB) ?_ ?_ eL norm
    · intro B n
      obtain ⟨P, f, hP, hf⟩ := flat_resolution (J := J) (R := R) B
      let := hf
      have hf' : QuasiIso (f⟦n⟧') := inferInstance
      have := (hmap _ _ (f⟦n⟧') hf').1
      refine ⟨P, f, hP, ?_⟩
      change IsIso (DerivedCategory.Q.map _)
      infer_instance
    · intro B hB n
      have hh := (hs A B hA hB n).2
      simpa only [Functor.flip_obj_obj,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
        Category.assoc, Functor.commShiftIso_map₂CochainComplex_hom_app,
        Functor.commShiftIso_map₂CochainComplex_flip_hom_app] using hh.symm
  · intro eR norm
    apply commShift_of_normalized_components
      (H := (tensorShiftTotal (R := R)).flip.obj A ⋙ DerivedCategory.Q)
      (F := DerivedCategory.Q ⋙ (siteRestrictionDerivedTensor (R := R)).flip.obj
        (DerivedCategory.Q.obj A)) (TensorFlatRepresentative (J := J) (R := R))
      stable (fun B hB ↦ tensorDescentPair.{u, v, r, w} (J := J) (R := R) B A hB hA) ?_ ?_ eR norm
    · intro B n
      obtain ⟨P, f, hP, hf⟩ := flat_resolution (J := J) (R := R) B
      let := hf
      have hf' : QuasiIso (f⟦n⟧') := inferInstance
      have := (hmap _ _ (f⟦n⟧') hf').2
      refine ⟨P, f, hP, ?_⟩
      change IsIso (DerivedCategory.Q.map _)
      infer_instance
    · intro B hB n
      have hh := (hs B A hB hA n).1
      simpa only [Functor.flip_obj_obj,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
        Category.assoc, Functor.commShiftIso_map₂CochainComplex_hom_app,
        Functor.commShiftIso_map₂CochainComplex_flip_hom_app] using hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The published derived tensor has unique normalized coherent signed integer shifts,
and every normalized fixed-factor comparison respects them.
Source: Stacks, Tag 0FNH (item-shift-tensor), Tags 06YS, 06YU and 04VK
(blueprint: lem-weil-pbc-derived-tensor-shift-descent).

Proof:
1. Localize the signed total tensor along the homotopy quotient in both variables,
   using the recorded complex comparison. The general bifunctor localization theorem
   preserves the zero, addition and mixed-sign identities.
2. Restrict this structure to the shift-stable resolving subcategory and postcompose
   with Qh. The recorded localization equivalence and derived comparison allow a second
   application of the same theorem, on the specified published derived tensor.
3. Paste the shift squares of the two comparison isomorphisms. Naturality of Qh's
   shift comparison identifies their composite with tensorDescentPair, including its
   canonical quotient-to-derived identifications. Every derived object has a resolving
   representative, so naturality along representative isomorphisms proves uniqueness.
4. A normalized fixed-factor comparison has the required square on resolving complexes.
   For an arbitrary complex choose a flat-term K-flat resolution, use naturality of
   that square, and cancel the invertible image of the shifted resolution map.
   The same argument in the other variable gives the other fixed-factor comparison.
-/
theorem derived_tensor_shift_descent
    (stable : ∀ (P : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
      TensorFlatRepresentative (J := J) (R := R) P →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (P⟦n⟧)) :
    ∃ s : (siteRestrictionDerivedTensor (J := J) (R := R)).CommShift₂Int,
      tensorResolvingShiftCompatible (J := J) (R := R) stable s ∧
      tensorShiftComparisonsUnique (J := J) (R := R) s ∧
      tensorFixedComparisonsShiftCompatible (J := J) (R := R) s := by
  let A := ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let qh := DerivedCategory.Qh.{w} (C := A)
  have h := site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R
  let P := tensorDescentClass.{u, v, r, w} (R := R)
  have hPmem : ∀ X, P X ↔ TensorFlatRepresentative (J := J) (R := R) X.as :=
    h.choose_spec.1
  let B := h.choose_spec.2.2.1.choose
  let c : q.prod q ⋙ B ≅ uncurry.obj (tensorShiftTotal (R := R)) ⋙ q :=
    tensorDescentComplexIso.{u, v, r, w} (R := R)
  let W := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  let L := P.ι ⋙ (qh : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
  let E := h.choose_spec.2.1.choose
  let : E.IsEquivalence := h.choose_spec.2.1.choose_spec.1
  have eL : W.Q ⋙ E ≅ L := h.choose_spec.2.1.choose_spec.2.some
  let : L.IsLocalization W :=
    Functor.IsLocalization.of_equivalence_target W.Q W L E.asEquivalence eL
  let U := siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R
  let d : P.ι.prod P.ι ⋙ B ⋙ qh ≅ L.prod L ⋙ U :=
    tensorDescentDerivedIso.{u, v, r, w} (R := R)
  have pair_hom (X Y : CochainComplex A ℤ)
      (hX : TensorFlatRepresentative (J := J) (R := R) X)
      (hY : TensorFlatRepresentative (J := J) (R := R) Y) :
      (tensorDescentPair (J := J) (R := R) X Y hX hY).hom =
        qh.map (c.inv.app (X, Y)) ≫
        d.hom.app (⟨q.obj X, (hPmem _).2 hX⟩, ⟨q.obj Y, (hPmem _).2 hY⟩) := by
    exact representativePair_hom (A := A) (tensorShiftTotal (R := R)) P
      (TensorFlatRepresentative (J := J) (R := R)) hPmem B U c d X Y hX hY
  obtain ⟨s, hnormalized⟩ := tensorShifts_normalized (tensorShiftTotal (R := R)) P
    (TensorFlatRepresentative (J := J) (R := R)) hPmem stable B U c d
    (tensorDescentPair (J := J) (R := R)) pair_hom
  have hnorm : tensorResolvingShiftCompatible (J := J) (R := R) stable s := by
    let := s
    intro X Y hX hY n
    simpa only [U, siteRestrictionDerivedTensor,
      Functor.commShiftIso_map₂CochainComplex_flip_hom_app,
      Functor.commShiftIso_map₂CochainComplex_hom_app] using hnormalized X Y hX hY n
  refine ⟨s, hnorm, tensor_shift_unique s ?_, tensor_fixed_shift stable s hnorm⟩
  intro M
  have := Localization.essSurj L W
  obtain ⟨p, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L M
  exact ⟨p.obj.as, (h.choose_spec.1 _).1 p.property, ⟨e⟩⟩

end

end SheafOfModules
