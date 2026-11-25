/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Adjunctions of derived functors

Given an adjunction `adj : f ⊣ g` of additive functors between abelian categories, this
file lifts `adj` through the stages of the derived formalism:

* `Adjunction.mapHomotopyCategory` (in
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`): the induced adjunction
  `f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c` between the homotopy categories,
  whenever the quotient functors to the homotopy categories are localizations with
  respect to homotopy equivalences (which holds, in particular, for the complex shapes
  `ComplexShape.up ℤ` and `ComplexShape.down ι`); it is obtained from the adjunction
  `Adjunction.mapHomologicalComplex` between the categories of homological complexes
  (`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`) by descent along the
  localization functors, using `Adjunction.localization`.
* `Adjunction.derivedAdjunction`: the derived adjunction

  `f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

  between the total derived functors on the unbounded derived categories, where

  - the source category is monoidal and admits functorial flat resolutions, and `f`
    preserves K-flat quasi-isomorphisms (`f.PreservesKFlatQuasiIso`), so that the total
    left derived functor is defined
    (see `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`);
  - the target category has K-injective resolutions, so that the total right derived
    functor is defined
    (see `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`).

  It is constructed by applying the abstract theorem `Adjunction.derived` to the
  adjunction `adj.mapHomotopyCategory (.up ℤ)`. The two "absoluteness" hypotheses of
  `Adjunction.derived` are verified using the good-object isomorphism criteria of the
  K-flat left derivability structure (for `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor`)
  and of the K-injective right derivability structure
  (for `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor`): in both cases, the comparison
  natural transformation is an isomorphism on K-flat (respectively K-injective) complexes
  because the counit `f.leftDerivedFunctorCounit` (respectively the unit
  `g.rightDerivedFunctorUnit`) is.
* `Adjunction.derivedAdjunctionPlus`: for `f` moreover *exact*, the bounded below
  derived adjunction `f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus`, obtained by
  restricting the derived adjunction along the inclusions of the bounded below derived
  categories, using the identification of the left derived functor of the exact functor
  `f` with `f.mapDerivedCategory` and the compatibility of `g.rightDerivedFunctorPlus`
  with the unbounded right derived functor.
* `Adjunction.derivedAdjunctionPlus_eq_derivedPlus`: the bounded below derived adjunction
  agrees with `Adjunction.derivedPlus`, constructed directly on the bounded below derived
  categories (`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`).
* `Adjunction.mapDerivedCategoryAdjunction` and
  `Adjunction.mapDerivedCategoryPlusAdjunction`: for `f` *and* `g` exact, the levelwise
  adjunctions `f.mapDerivedCategory ⊣ g.mapDerivedCategory` on the unbounded derived
  categories and `f.mapDerivedCategoryPlus ⊣ g.mapDerivedCategoryPlus` on the bounded
  below ones. These are `Adjunction.derivedAdjunction` transported along the two
  identifications of a derived functor of an exact functor with the levelwise functor,
  `Functor.leftDerivedFunctorIsoMapDerivedCategory` and
  `Functor.rightDerivedFunctorIsoMapDerivedCategory`, and then restricted along the
  inclusions of the bounded below derived categories. Note that `g` being exact does not
  make the identification of `g.rightDerivedFunctor` with `g.mapDerivedCategory`
  hypothesis-free: it still goes through the K-injective resolutions used to define the
  total right derived functor.
* `Adjunction.isIso_mapDerivedCategoryAdjunction_unit` and
  `Adjunction.isIso_mapDerivedCategoryAdjunction_counit`: the unit (respectively counit) of
  `f.mapDerivedCategory ⊣ g.mapDerivedCategory` is an isomorphism if that of `f ⊣ g` is.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

section MapHomotopyCategory

variable {ι : Type*} {V W : Type*} [Category V] [Category W]
  [Preadditive V] [Preadditive W]
  {f : V ⥤ W} {g : W ⥤ V} [f.Additive] [g.Additive]

variable (f) in
/-- The 2-commutative square expressing that `Functor.mapHomotopyCategory`
descends `Functor.mapHomologicalComplex` along the quotient functors to the
homotopy categories. -/
instance Functor.catCommSqMapHomotopyCategory (c : ComplexShape ι) :
    CatCommSq (f.mapHomologicalComplex c) (HomotopyCategory.quotient V c)
      (HomotopyCategory.quotient W c) (f.mapHomotopyCategory c) :=
  ⟨(f.mapHomotopyCategoryFactors c).symm⟩

/-! The adjunction `f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c` induced on the
homotopy categories is `CategoryTheory.Adjunction.mapHomotopyCategory` of
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`. -/

end MapHomotopyCategory

section DerivedAdjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

namespace Functor

/-- The composition `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor` is the
left derived functor of `(f.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
⋙ g.rightDerivedFunctor`: the required comparison natural transformation is
an isomorphism on K-flat complexes since `f.leftDerivedFunctorCounit` is.
This is the first "absoluteness" hypothesis of `Adjunction.derived`. -/
instance isLeftDerivedFunctor_leftDerivedFunctor_comp_rightDerivedFunctor :
    (f.leftDerivedFunctor ⋙ g.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight f.leftDerivedFunctorCounit g.rightDerivedFunctor)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).localizerMorphismKFlat
    |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure _
      (fun P ↦ f.derives_kFlat.isIso_of_isLeftDerivedFunctor _ P) _

/-- The composition `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor` is the
right derived functor of `(g.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
⋙ f.leftDerivedFunctor`: the required comparison natural transformation is
an isomorphism on K-injective complexes since `g.rightDerivedFunctorUnit` is.
This is the second "absoluteness" hypothesis of `Adjunction.derived`. -/
instance isRightDerivedFunctor_rightDerivedFunctor_comp_leftDerivedFunctor :
    (g.rightDerivedFunctor ⋙ f.leftDerivedFunctor).IsRightDerivedFunctor
      (whiskerRight g.rightDerivedFunctorUnit f.leftDerivedFunctor ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism D)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

end Functor

/-- The derived adjunction: an adjunction `f ⊣ g` of additive functors between
abelian categories, where `f` is left derivable via K-flat resolutions and `g`
is right derivable via K-injective resolutions, induces an adjunction

`f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

between the total derived functors on the unbounded derived categories. -/
noncomputable def Adjunction.derivedAdjunction {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso] :
    f.leftDerivedFunctor ⊣ g.rightDerivedFunctor :=
  (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
    f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit

/-- The bounded below derived adjunction of an adjoint pair `adj : f ⊣ g` of additive
functors between abelian categories, where `f` is moreover *exact*:

`f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus`

between the functor induced by `f` on the bounded below derived categories and the right
derived functor of `g` on the bounded below derived categories. It is obtained by
restricting the unbounded derived adjunction `Adjunction.derivedAdjunction` along the
inclusions of the bounded below derived categories: since `f` is exact, its total left
derived functor identifies with `f.mapDerivedCategory`
(`Functor.leftDerivedFunctorIsoMapDerivedCategory`), which restricts to the bounded
below derived categories as `f.mapDerivedCategoryPlus`; on the right adjoint side, the
restriction of `g.rightDerivedFunctor` identifies with `g.rightDerivedFunctorPlus` by
`Functor.rightDerivedFunctorPlusCompatibility`. -/
noncomputable def Adjunction.derivedAdjunctionPlus {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [EnoughInjectives D] :
    f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus :=
  Adjunction.restrictFullyFaithful
    (adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    f.mapDerivedCategoryPlusCompatibility.symm
    g.rightDerivedFunctorPlusCompatibility.symm

/-- The levelwise derived adjunction of an adjoint pair `adj : f ⊣ g` of *exact*
functors between abelian categories:

`f.mapDerivedCategory ⊣ g.mapDerivedCategory`

between the functors induced on the unbounded derived categories by applying `f` and `g`
levelwise. It is the unbounded derived adjunction `Adjunction.derivedAdjunction`
transported along the identifications of the total derived functors of the exact `f` and
`g` with the levelwise functors,
`Functor.leftDerivedFunctorIsoMapDerivedCategory` and
`Functor.rightDerivedFunctorIsoMapDerivedCategory`. -/
noncomputable def Adjunction.mapDerivedCategoryAdjunction {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] :
    f.mapDerivedCategory ⊣ g.mapDerivedCategory :=
  (adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory).ofNatIsoRight
    g.rightDerivedFunctorIsoMapDerivedCategory

/-- The unit of `f.mapDerivedCategory ⊣ g.mapDerivedCategory` is an isomorphism if the unit
of `f ⊣ g` is. -/
instance Adjunction.isIso_mapDerivedCategoryAdjunction_unit {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] [IsIso adj.unit] :
    IsIso adj.mapDerivedCategoryAdjunction.unit := by
  -- `f.mapDerivedCategory ⋙ g.mapDerivedCategory ≅ (f ⋙ g).mapDerivedCategory ≅ 𝟭`, so
  -- `f.mapDerivedCategory` is fully faithful.
  have h := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfCompIsoId
    (Functor.mapDerivedCategoryCompIso f g ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := h.full
  have := h.faithful
  infer_instance

/-- The counit of `f.mapDerivedCategory ⊣ g.mapDerivedCategory` is an isomorphism if the
counit of `f ⊣ g` is. -/
instance Adjunction.isIso_mapDerivedCategoryAdjunction_counit {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] [IsIso adj.counit] :
    IsIso adj.mapDerivedCategoryAdjunction.counit := by
  -- `g.mapDerivedCategory ⋙ f.mapDerivedCategory ≅ (g ⋙ f).mapDerivedCategory ≅ 𝟭`, so
  -- `g.mapDerivedCategory` is fully faithful.
  have h := adj.mapDerivedCategoryAdjunction.fullyFaithfulROfCompIsoId
    (Functor.mapDerivedCategoryCompIso g f ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.counit) ≪≫
        Functor.mapDerivedCategoryIdIso D)
  have := h.full
  have := h.faithful
  infer_instance

/-- The bounded below levelwise derived adjunction of an adjoint pair `adj : f ⊣ g` of
*exact* functors between abelian categories:

`f.mapDerivedCategoryPlus ⊣ g.mapDerivedCategoryPlus`

obtained from `Adjunction.mapDerivedCategoryAdjunction` by restriction along the fully
faithful inclusions of the bounded below derived categories, which is legitimate since an
exact functor preserves bounded below objects
(`Functor.mapDerivedCategoryPlusCompatibility`). -/
noncomputable def Adjunction.mapDerivedCategoryPlusAdjunction {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g] :
    f.mapDerivedCategoryPlus ⊣ g.mapDerivedCategoryPlus :=
  Adjunction.restrictFullyFaithful adj.mapDerivedCategoryAdjunction
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    f.mapDerivedCategoryPlusCompatibility.symm
    g.mapDerivedCategoryPlusCompatibility.symm

/-- The unit of the levelwise derived adjunction `Adjunction.mapDerivedCategoryAdjunction` is,
on the image of a complex `K` and modulo the factorizations `Functor.mapDerivedCategoryFactorsh`,
the levelwise unit of `adj`. -/
theorem Adjunction.mapDerivedCategoryAdjunction_unit_app_fac {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj K) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.hom.app K) ≫
        g.mapDerivedCategoryFactorsh.hom.app ((f.mapHomotopyCategory _).obj K) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K) := by
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit K
  have h₂ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
  have h₃ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory _).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂ h₃
  have h₄ := g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (f.mapDerivedCategoryFactorsh.hom.app K)
  simp only [Adjunction.mapDerivedCategoryAdjunction, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₄]
  rw [← Functor.map_comp_assoc, h₂]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The unit of the bounded below levelwise derived adjunction
`Adjunction.mapDerivedCategoryPlusAdjunction` is, on the image of a bounded below complex `K` and
modulo the factorizations `Functor.mapDerivedCategoryPlusFactorsh`, the levelwise unit of `adj`.
-/
theorem Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac {f : C ⥤ D} {g : D ⥤ C}
    (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (K : HomotopyCategory.Plus C) :
    adj.mapDerivedCategoryPlusAdjunction.unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        g.mapDerivedCategoryPlus.map (f.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        g.mapDerivedCategoryPlusFactorsh.hom.app (f.mapHomotopyCategoryPlus.obj K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := adj.mapDerivedCategoryAdjunction_unit_app_fac K.obj
  rw [Functor.map_comp, Functor.map_comp, Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  erw [Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have e : DerivedCategory.Plus.ι.map
      (g.mapDerivedCategoryPlus.map (f.mapDerivedCategoryPlusFactorsh.hom.app K)) =
      g.mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (f.mapDerivedCategoryPlusFactorsh.hom.app K)) := rfl
  have e₂ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
        (adj.mapHomotopyCategoryPlus.unit.app K)) := rfl
  rw [e, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app, e₂,
    Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app, ← h]
  rfl

/-- The unit of the bounded below derived adjunction `Adjunction.derivedAdjunctionPlus` is
computed on the image of a bounded below complex `K` by the unit of `adj` followed by the unit of
the right derived functor, as for `Adjunction.derivedPlus` (`Adjunction.derivedPlus_unit_app_fac`).
-/
theorem Adjunction.derivedAdjunctionPlus_unit_app_fac {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [EnoughInjectives D] (K : HomotopyCategory.Plus C) :
    adj.derivedAdjunctionPlus.unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.hom.app K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.ofNatIsoLeft_unit]
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit ((HomotopyCategory.Plus.ι C).obj K)
  have h₂ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.Plus.ι C).obj K)
  have h₃ : g.rightDerivedFunctorPlusιUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
      g.rightDerivedFunctorPlusCompatibility.hom.app
        (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h₄ : DerivedCategory.Plus.ι.map
      (g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj K)) =
      g.ιRightDerivedFunctorUnit.app (f.mapHomotopyCategoryPlus.obj K) ≫
        g.rightDerivedFunctorPlusCompatibility.inv.app
          (DerivedCategory.Plus.Qh.obj (f.mapHomotopyCategoryPlus.obj K)) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₅ := g.rightDerivedFunctorPlusCompatibility.inv.naturality
    (f.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h₅
  have h₆ : f.mapDerivedCategoryPlusCompatibility.symm.hom.app (DerivedCategory.Plus.Qh.obj K) =
      𝟙 _ := rfl
  have h₇ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategory (ComplexShape.up ℤ) adj).unit.app
        ((HomotopyCategory.Plus.ι C).obj K)) := by
    have : (HomotopyCategory.Plus.ι C).map (adj.mapHomotopyCategoryPlus.unit.app K) =
        (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.Plus.ι C).obj K) := by
      dsimp only [Adjunction.mapHomotopyCategoryPlus]
      erw [Adjunction.map_restrictFullyFaithful_unit_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact Category.comp_id _
    exact congrArg DerivedCategory.Qh.map this
  have h₈ : (adj.derivedAdjunction.unit ≫
      Functor.whiskerRight f.leftDerivedFunctorIsoMapDerivedCategory.hom g.rightDerivedFunctor).app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      g.rightDerivedFunctor.map (f.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.Plus.ι C).obj K)) =
      DerivedCategory.Qh.map ((Adjunction.mapHomotopyCategory (ComplexShape.up ℤ) adj).unit.app
        ((HomotopyCategory.Plus.ι C).obj K)) ≫
      g.rightDerivedFunctorUnit.app
        ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.Plus.ι C).obj K)) := by
    rw [← h₁, ← h₂]
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rfl
  rw [h₄, h₇]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.assoc, ← h₅, ← Category.assoc, h₈, Category.assoc]
  rfl

/-- The two constructions of the bounded below derived adjunction
`f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus` agree: the restriction
`Adjunction.derivedAdjunctionPlus` of the unbounded derived adjunction is
`Adjunction.derivedPlus`, constructed directly on the bounded below categories. Both units satisfy
the formula characterising the unit (`Adjunction.derivedPlus_unit_eq`). -/
theorem Adjunction.derivedAdjunctionPlus_eq_derivedPlus {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [EnoughInjectives D] :
    adj.derivedAdjunctionPlus = adj.derivedPlus :=
  Adjunction.ext (Adjunction.derivedPlus_unit_eq adj _
    (adj.derivedAdjunctionPlus_unit_app_fac))

end DerivedAdjunction

end CategoryTheory
