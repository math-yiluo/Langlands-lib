/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The bounded below derived adjunction of an adjunction with exact left adjoint

Let `L ⊣ R` be an adjunction of additive functors between abelian categories, with `L`
exact and the target of `L` having enough injectives. Then `L` induces a functor
`L.mapDerivedCategoryPlus` on the bounded below derived categories by applying it
levelwise, `R` has a bounded below right derived functor `R.rightDerivedFunctorPlus`, and
we show that these two are again adjoint. In particular the adjunction has a unit

`𝟭 ⟶ L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus`,

which is what the comparison of derived lower shrieks along a refinement of
compactifications is built from.

We also prove the identity and composition laws for the derived unit. For the identity
adjunction the derived unit is the identity, modulo
`Functor.mapDerivedCategoryPlusIdIso` and `Functor.rightDerivedFunctorPlusIdIso`; for a
composite of adjunctions the derived unit is the composite of the two derived units, modulo
`Functor.mapDerivedCategoryPlusCompIso` and `Functor.rightDerivedFunctorPlusCompIso`. Both
reduce, through `CategoryTheory.Adjunction.derivedPlus_unit_eq`, to the corresponding laws
for `CategoryTheory.Adjunction.mapHomotopyCategoryPlus` together with the characterizations
of the four comparison isomorphisms.

## Main definitions

- `CategoryTheory.Adjunction.derivedPlus`: the adjunction
  `L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus`.
- `CategoryTheory.Adjunction.derivedPlus_unit_app_fac` and
  `CategoryTheory.Adjunction.derivedPlus_unit_eq`: the formula computing the unit on the
  image of a bounded below complex, and the fact that this formula characterises it.

## Main results

- `CategoryTheory.Adjunction.derivedPlus_id_unit` and
  `CategoryTheory.Adjunction.derivedPlus_id_unit_app`: the identity law.
- `CategoryTheory.Adjunction.derivedPlus_comp_unit` and
  `CategoryTheory.Adjunction.derivedPlus_comp_unit_app`: the composition law.
- `CategoryTheory.Adjunction.derivedPlus_unit_comp` and
  `CategoryTheory.Adjunction.derivedPlus_unit_comp_app`: if two adjunctions `LA ⊣ RA` and
  `LB ⊣ RB` between the same pair of categories come with isomorphisms `u : LA ≅ LB` and
  `l : RB ≅ RA` corresponding to each other under conjugation, then the same relation
  holds for the bounded below derived adjunctions.
- `CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac`: the mate of a square of derived
  functors with respect to the bounded below derived adjunctions is computed on complexes by the
  mate of the underived square.

## The proof

The construction is Mathlib's `CategoryTheory.Adjunction.derived`, which produces an
adjunction between a left derived functor and a right derived functor as soon as the two
composites are again derived functors ("absoluteness"), applied to the adjunction
`L.mapHomotopyCategoryPlus ⊣ R.mapHomotopyCategoryPlus` on the bounded below homotopy
categories. There are two absoluteness statements to check, and they are of a different
nature:

* `L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus` is the left derived functor of
  `L.mapHomotopyCategoryPlus ⋙ Qh ⋙ R.rightDerivedFunctorPlus` because the comparison map
  is an isomorphism, `L` being exact: no resolutions are involved.
* `R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus` is the right derived functor of
  `R.mapHomotopyCategoryPlus ⋙ Qh ⋙ L.mapDerivedCategoryPlus` by the injective right
  derivability structure: the comparison map is `L.mapDerivedCategoryPlus` applied to the
  unit of `R.rightDerivedFunctorPlus`, which is an isomorphism on bounded below complexes
  of injectives.

Like `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`, this
file deliberately avoids the unbounded machinery indexed by K-injective complexes. That
machinery is proved, not assumed — `HasKInjectiveResolutions` holds in every Grothendieck
abelian category (`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`)
— but it is not implied by enough injectives, which is all the bounded below statement needs,
so this file does not import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

instance isLeftDerivedFunctor_mapDerivedCategoryPlus :
    L.mapDerivedCategoryPlus.IsLeftDerivedFunctor L.mapDerivedCategoryPlusFactorsh.hom
      (HomotopyCategory.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryPlusFactorsh

instance isLeftDerivedFunctor_mapDerivedCategoryPlus_comp :
    (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)

instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp :
    (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso D) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
      L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  have : IsIso (R.rightDerivedFunctorPlusUnith.app
    ((InjectiveObject.ι D).mapHomotopyCategoryPlus.obj X₁)) := inferInstance
  dsimp
  infer_instance

/-- The bounded below derived adjunction: for an adjunction `L ⊣ R` of additive functors
between abelian categories with `L` exact, the functor `L.mapDerivedCategoryPlus` induced
by `L` on the bounded below derived categories is left adjoint to the bounded below right
derived functor `R.rightDerivedFunctorPlus` of `R`. -/
noncomputable def derivedPlus :
    L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
  adj.mapHomotopyCategoryPlus.derived
    (HomotopyCategory.Plus.quasiIso C) (HomotopyCategory.Plus.quasiIso D)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith

/-- The unit of the bounded below derived adjunction is determined by the unit of `adj`:
on the image of a bounded below complex `K`, it is the unit of `adj` on `K` followed by the
unit of the right derived functor of `R` at `L(K)`. -/
@[reassoc]
lemma derivedPlus_unit_app_fac (K : HomotopyCategory.Plus C) :
    adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K) :=
  adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso C)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith K

/-- The counit of the bounded below derived adjunction is determined by the counit of
`adj`, dually to `Adjunction.derivedPlus_unit_app_fac`. -/
@[reassoc]
lemma derivedPlus_counit_app_fac (M : HomotopyCategory.Plus D) :
    L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app M) ≫
        adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj M) =
      L.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj M) ≫
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app M) :=
  adj.mapHomotopyCategoryPlus.derivedε_fac_app (HomotopyCategory.Plus.quasiIso D)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith M

/-- The formula of `Adjunction.derivedPlus_unit_app_fac` characterises the unit of the
bounded below derived adjunction: `L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus`
is a left derived functor, so a natural transformation into it is determined by its
components on the images of the bounded below homotopy category. -/
lemma derivedPlus_unit_eq
    (η : 𝟭 (DerivedCategory.Plus C) ⟶
      L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (h : ∀ K : HomotopyCategory.Plus C,
      η.app (DerivedCategory.Plus.Qh.obj K) ≫
          R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) =
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
          R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K)) :
    η = adj.derivedPlus.unit := by
  refine Functor.leftDerived_ext _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simpa using (h K).trans (adj.derivedPlus_unit_app_fac K).symm

section Identity

variable (C)

/-- **The identity law for the bounded below derived unit**: the unit of the bounded below
derived adjunction of `Adjunction.id` is the identity, modulo the identity isomorphisms
`Functor.mapDerivedCategoryPlusIdIso` and `Functor.rightDerivedFunctorPlusIdIso`. -/
theorem derivedPlus_id_unit [EnoughInjectives C] :
    (Adjunction.id (C := C)).derivedPlus.unit =
      (Functor.mapDerivedCategoryPlusIdIso C).inv ≫
        Functor.whiskerLeft (𝟭 C).mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusIdIso C).inv := by
  refine ((Adjunction.id (C := C)).derivedPlus_unit_eq _ ?_).symm
  intro K
  have hαf : (𝟭 C).mapDerivedCategoryPlusFactorsh.hom.app K =
      (Functor.mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusIdIso C).inv.app K) := by
    rw [Functor.mapDerivedCategoryPlusIdIso_fac_app, Category.assoc, ← Functor.map_comp]
    simp
  have hu : (𝟭 C).rightDerivedFunctorPlusUnith.app ((𝟭 C).mapHomotopyCategoryPlus.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusIdIso C).hom.app
            ((𝟭 C).mapHomotopyCategoryPlus.obj K)) ≫
        (Functor.rightDerivedFunctorPlusIdIso C).inv.app
          (DerivedCategory.Plus.Qh.obj ((𝟭 C).mapHomotopyCategoryPlus.obj K)) := by
    rw [← Functor.rightDerivedFunctorPlusIdIso_fac_app]
    simp
  rw [mapHomotopyCategoryPlus_id_unit_app, hu, hαf]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality]
  simp only [Functor.id_map, Functor.comp_obj, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, NatTrans.naturality, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp]

/-- The pointwise form of `Adjunction.derivedPlus_id_unit`. -/
@[reassoc]
theorem derivedPlus_id_unit_app [EnoughInjectives C] (X : DerivedCategory.Plus C) :
    (Adjunction.id (C := C)).derivedPlus.unit.app X ≫
        (Functor.rightDerivedFunctorPlusIdIso C).hom.app
          ((𝟭 C).mapDerivedCategoryPlus.obj X) ≫
        (Functor.mapDerivedCategoryPlusIdIso C).hom.app X = 𝟙 X := by
  rw [derivedPlus_id_unit]
  simp

end Identity

section Conjugate

variable {LA LB : C ⥤ D} {RA RB : D ⥤ C} [LA.Additive] [RA.Additive] [LB.Additive]
  [RB.Additive] [PreservesFiniteLimits LA] [PreservesFiniteColimits LA]
  [PreservesFiniteLimits LB] [PreservesFiniteColimits LB]
  (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) (u : LA ≅ LB) (l : RB ≅ RA)
  (h : ∀ M, adjA.unit.app M ≫ RA.map (u.hom.app M) = adjB.unit.app M ≫ l.hom.app (LB.obj M))

include h in
/-- **Transport of a conjugation relation to the bounded below derived adjunctions**: if
`u : LA ≅ LB` and `l : RB ≅ RA` satisfy the unit relation
`adjA.unit ≫ RA(u) = adjB.unit ≫ l` for two adjunctions `LA ⊣ RA`, `LB ⊣ RB` with exact left
adjoints between the same pair of categories, then the units of the bounded below derived
adjunctions satisfy the same relation. -/
theorem derivedPlus_unit_comp :
    adjA.derivedPlus.unit ≫ Functor.whiskerRight
        (Functor.mapDerivedCategoryPlusNatIso u).hom RA.rightDerivedFunctorPlus =
      adjB.derivedPlus.unit ≫ Functor.whiskerLeft LB.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusNatTrans l.hom) := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (RA.rightDerivedFunctorPlus.map
    (LB.mapDerivedCategoryPlusFactorsh.hom.app K))]
  have hnatU : RA.rightDerivedFunctorPlusUnith.app (LA.mapHomotopyCategoryPlus.obj K) ≫
      RA.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus u.hom).app K)) =
      DerivedCategory.Plus.Qh.map (RA.mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus u.hom).app K)) ≫
        RA.rightDerivedFunctorPlusUnith.app (LB.mapHomotopyCategoryPlus.obj K) :=
    (RA.rightDerivedFunctorPlusUnith.naturality _).symm
  have hnatL : (Functor.rightDerivedFunctorPlusNatTrans l.hom).app
        (LB.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      RA.rightDerivedFunctorPlus.map (LB.mapDerivedCategoryPlusFactorsh.hom.app K) =
      RB.rightDerivedFunctorPlus.map (LB.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (Functor.rightDerivedFunctorPlusNatTrans l.hom).app
          (DerivedCategory.Plus.Qh.obj (LB.mapHomotopyCategoryPlus.obj K)) :=
    ((Functor.rightDerivedFunctorPlusNatTrans l.hom).naturality _).symm
  trans DerivedCategory.Plus.Qh.map (adjA.mapHomotopyCategoryPlus.unit.app K) ≫
    DerivedCategory.Plus.Qh.map (RA.mapHomotopyCategoryPlus.map
      ((NatTrans.mapHomotopyCategoryPlus u.hom).app K)) ≫
    RA.rightDerivedFunctorPlusUnith.app (LB.mapHomotopyCategoryPlus.obj K)
  · rw [Category.assoc, ← Functor.map_comp,
      Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh, Functor.map_comp,
      derivedPlus_unit_app_fac_assoc, hnatU]
  · rw [Category.assoc, hnatL, derivedPlus_unit_app_fac_assoc,
      Functor.rightDerivedFunctorPlusNatTrans_app,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      mapHomotopyCategoryPlus_unit_app_comp adjA adjB u.hom l.hom h K]

include h in
/-- The pointwise form of `Adjunction.derivedPlus_unit_comp`. -/
@[reassoc]
theorem derivedPlus_unit_comp_app (X : DerivedCategory.Plus C) :
    adjA.derivedPlus.unit.app X ≫
        RA.rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusNatIso u).hom.app X) =
      adjB.derivedPlus.unit.app X ≫
        (Functor.rightDerivedFunctorPlusNatTrans l.hom).app
          (LB.mapDerivedCategoryPlus.obj X) :=
  NatTrans.congr_app (derivedPlus_unit_comp adjA adjB u l h) X

end Conjugate

section Composition

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory E]
  [EnoughInjectives E] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [R₂.PreservesInjectiveObjects]

/-- **The composition law for the bounded below derived unit**: the unit of the bounded
below derived adjunction of a composite `adj₁.comp adj₂` is the composite of the two derived
units, modulo the composition isomorphisms `Functor.mapDerivedCategoryPlusCompIso` and
`Functor.rightDerivedFunctorPlusCompIso`.

The hypothesis `R₂.PreservesInjectiveObjects`, which is what
`Functor.rightDerivedFunctorPlusCompIso` needs, follows from the exactness of `L₂` by
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj₂`. -/
theorem derivedPlus_comp_unit :
    (adj₁.comp adj₂).derivedPlus.unit =
      adj₁.derivedPlus.unit ≫
        Functor.whiskerLeft L₁.mapDerivedCategoryPlus
          (Functor.whiskerRight adj₂.derivedPlus.unit R₁.rightDerivedFunctorPlus) ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIso L₁ L₂).inv
          (R₂.rightDerivedFunctorPlus ⋙ R₁.rightDerivedFunctorPlus) ≫
        Functor.whiskerLeft (L₁ ⋙ L₂).mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso R₂ R₁).inv := by
  refine ((adj₁.comp adj₂).derivedPlus_unit_eq _ ?_).symm
  intro K
  have hw : (R₂ ⋙ R₁).rightDerivedFunctorPlusUnith.app
        ((L₁ ⋙ L₂).mapHomotopyCategoryPlus.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit R₂ R₁).app
          ((L₁ ⋙ L₂).mapHomotopyCategoryPlus.obj K) ≫
        (Functor.rightDerivedFunctorPlusCompIso R₂ R₁).inv.app
          (DerivedCategory.Plus.Qh.obj ((L₁ ⋙ L₂).mapHomotopyCategoryPlus.obj K)) := by
    rw [← Functor.rightDerivedFunctorPlusCompIso_fac_app]
    simp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Category.assoc]
  rw [← NatTrans.naturality, hw, mapHomotopyCategoryPlus_comp_unit_app]
  simp only [Functor.comp_obj, ← Category.assoc]
  congr 1
  simp only [Functor.rightDerivedFunctorPlusCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Category.assoc, Category.id_comp,
    Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusCompIso_fac L₁ L₂ K]
  simp only [Functor.comp_map, Functor.map_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc,
    NatTrans.naturality, Functor.comp_map, Iso.hom_inv_id_app_assoc]
  have hin : adj₂.derivedPlus.unit.app
        (L₁.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      R₂.rightDerivedFunctorPlus.map
        (L₂.mapDerivedCategoryPlus.map (L₁.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
          L₂.mapDerivedCategoryPlusFactorsh.hom.app (L₁.mapHomotopyCategoryPlus.obj K) ≫
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K)) =
      L₁.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map
          (adj₂.mapHomotopyCategoryPlus.unit.app (L₁.mapHomotopyCategoryPlus.obj K) ≫
            R₂.mapHomotopyCategoryPlus.map
              ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K)) ≫
        R₂.rightDerivedFunctorPlusUnith.app ((L₁ ⋙ L₂).mapHomotopyCategoryPlus.obj K) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.comp_map L₂.mapDerivedCategoryPlus R₂.rightDerivedFunctorPlus,
      ← NatTrans.naturality_assoc]
    simp only [Functor.id_map, Functor.comp_obj]
    rw [derivedPlus_unit_app_fac_assoc,
      ← Functor.comp_map DerivedCategory.Plus.Qh R₂.rightDerivedFunctorPlus,
      ← NatTrans.naturality, Functor.comp_map]
  rw [hin]
  have hv₁ : R₁.rightDerivedFunctorPlusUnith.app (L₁.mapHomotopyCategoryPlus.obj K) ≫
      R₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        (adj₂.mapHomotopyCategoryPlus.unit.app (L₁.mapHomotopyCategoryPlus.obj K) ≫
          R₂.mapHomotopyCategoryPlus.map
            ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K))) =
      DerivedCategory.Plus.Qh.map (R₁.mapHomotopyCategoryPlus.map
        (adj₂.mapHomotopyCategoryPlus.unit.app (L₁.mapHomotopyCategoryPlus.obj K) ≫
          R₂.mapHomotopyCategoryPlus.map
            ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L₁ ⋙ L₂))).hom.app K))) ≫
      R₁.rightDerivedFunctorPlusUnith.app
        (R₂.mapHomotopyCategoryPlus.obj ((L₁ ⋙ L₂).mapHomotopyCategoryPlus.obj K)) :=
    (R₁.rightDerivedFunctorPlusUnith.naturality _).symm
  rw [Functor.map_comp, derivedPlus_unit_app_fac_assoc, Functor.map_comp,
    reassoc_of% hv₁]
  simp only [Functor.map_comp, Category.assoc]

/-- The pointwise form of `Adjunction.derivedPlus_comp_unit`. -/
@[reassoc]
theorem derivedPlus_comp_unit_app (X : DerivedCategory.Plus C) :
    (adj₁.comp adj₂).derivedPlus.unit.app X ≫
        (Functor.rightDerivedFunctorPlusCompIso R₂ R₁).hom.app
          ((L₁ ⋙ L₂).mapDerivedCategoryPlus.obj X) ≫
        R₁.rightDerivedFunctorPlus.map (R₂.rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusCompIso L₁ L₂).hom.app X)) =
      adj₁.derivedPlus.unit.app X ≫
        R₁.rightDerivedFunctorPlus.map
          (adj₂.derivedPlus.unit.app (L₁.mapDerivedCategoryPlus.obj X)) := by
  rw [derivedPlus_comp_unit]
  simp

end Composition

section Mates

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄] [EnoughInjectives C₁] [EnoughInjectives C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **The derived mate is computed by the underived mate on complexes.** Let `L ⊣ R` and
`L' ⊣ R'` be adjunctions with exact left adjoints, `G` and `G'` exact functors, and
`σ : G ⋙ L' ⟶ L ⋙ G'` a square. Let `θ` be a square of the induced functors on the bounded below
derived categories which is computed by `σ` on complexes (hypothesis `hθ`). Then the mate of `θ`
with respect to the bounded below derived adjunctions `Adjunction.derivedPlus`, restricted along
the unit `R(K) ⟶ R⁺(K)` of the derived functor, is the underived mate of `σ` followed by the unit
`R'(G'K) ⟶ R'⁺(G'K)`. This is the form in which a natural transformation out of the right
derived functor `R⁺ ⋙ G⁺` is characterised (`Functor.rightDerived_ext`). -/
theorem derivedPlus_mateEquiv_app_fac (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus L'.mapDerivedCategoryPlus
      G'.mapDerivedCategoryPlus)
    (hθ : ∀ N : HomotopyCategory.Plus C₂,
      θ.app (DerivedCategory.Plus.Qh.obj N) ≫
          G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
        L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app N))
    (K : HomotopyCategory.Plus C₁) :
    G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app K) ≫
        (mateEquiv adj.derivedPlus adj'.derivedPlus θ).app
          (DerivedCategory.Plus.Qh.obj K) =
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (mateEquiv adj adj' σ)).app K) ≫
        R'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        R'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have hmate : ∀ (Z : DerivedCategory.Plus C₁),
      (mateEquiv adj.derivedPlus adj'.derivedPlus θ).app Z =
        adj'.derivedPlus.unit.app
            (G.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj Z)) ≫
          R'.rightDerivedFunctorPlus.map (θ.app (R.rightDerivedFunctorPlus.obj Z)) ≫
          R'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlus.map
            (adj.derivedPlus.counit.app Z)) := fun Z => by
    simp [mateEquiv_apply]
  set N := R.mapHomotopyCategoryPlus.obj K
  set u := R.rightDerivedFunctorPlusUnith.app K
  have h₁ := adj'.derivedPlus.unit.naturality (G.mapDerivedCategoryPlus.map u)
  have h₂ := θ.naturality u
  have h₃ := adj.derivedPlus_counit_app_fac K
  have h₄ := NatTrans.mapHomotopyCategoryPlus_mateEquiv_app adj adj' σ K
  have h₅ := R'.rightDerivedFunctorPlusUnith.naturality
    ((NatTrans.mapHomotopyCategoryPlus σ).app N ≫
      G'.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app K))
  have h₆ := adj'.derivedPlus_unit_app_fac (G.mapHomotopyCategoryPlus.obj N)
  have h₇ := adj'.derivedPlus.unit.naturality (G.mapDerivedCategoryPlusFactorsh.hom.app N)
  have h₈ := hθ N
  have h₉ := G'.mapDerivedCategoryPlusFactorsh.hom.naturality
    (adj.mapHomotopyCategoryPlus.counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₅ h₇ h₉
  rw [hmate, reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp (G'.mapDerivedCategoryPlus), h₃, h₄]
  erw [← Functor.map_comp R'.mapHomotopyCategoryPlus]
  erw [Functor.map_comp DerivedCategory.Plus.Qh, Category.assoc, reassoc_of% h₅]
  erw [← reassoc_of% h₆, reassoc_of% h₇]
  congr 1
  have key : θ.app (DerivedCategory.Plus.Qh.obj N) ≫
      G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N ≫
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app K)) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ).app N) ≫
        DerivedCategory.Plus.Qh.map
          (G'.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app K)) ≫
        G'.mapDerivedCategoryPlusFactorsh.inv.app K := by
    rw [← cancel_mono (G'.mapDerivedCategoryPlusFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    rw [h₉, reassoc_of% h₈]
    erw [Category.comp_id]
  rw [key]
  simp only [Functor.map_comp]
  simp only [Category.assoc]

end Mates

end CategoryTheory.Adjunction
