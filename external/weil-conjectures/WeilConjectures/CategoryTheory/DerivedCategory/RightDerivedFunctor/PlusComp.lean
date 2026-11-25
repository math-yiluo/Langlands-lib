/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Composition of right derived functors on bounded below derived categories

This is the bounded below counterpart of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`. Let `F : C ⥤ D` and
`G : D ⥤ E` be additive functors between abelian categories, with `C` and `D` having
enough injectives. If `F` preserves injective objects, then the canonical comparison

`R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`

is an isomorphism (`Functor.rightDerivedFunctorPlusCompIso`).

## Why this is not a corollary of the unbounded statement

`Functor.rightDerivedFunctorCompIso` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` proves the same
theorem for the unbounded derived category, but it assumes `HasKInjectiveResolutions` on
both `C` and `D`, whose only source in this repository is a `sorry`. The bounded below
statement needs only
enough injectives, so it rests on proved theorems; see
`WeilConjectures.SixFunctors.Etale.Derived` for why that distinction matters here. This file
therefore deliberately does not import anything from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.

## The proof, and where it differs from the unbounded one

The shape is the same: the composite `R⁺F ⋙ R⁺G`, equipped with the composite unit
`Functor.rightDerivedFunctorPlusCompUnit`, is itself a right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`, and the isomorphism then follows from uniqueness
of right derived functors.

The hypothesis on `F` is where the two arguments part company. The unbounded derivability
structure is indexed by K-injective complexes, so there the requirement is that `F` send
K-injective complexes to K-injective complexes
(`Functor.PreservesKInjectiveComplexes`). The bounded below derivability structure is
indexed by bounded below complexes of *injective objects*, so here the requirement is only
that `F` preserve injective objects — Mathlib's `Functor.PreservesInjectiveObjects`, which
for a right adjoint of a monomorphism-preserving functor is
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. That is a
weaker and much more readily available hypothesis than the K-injective one, which needs the
left adjoint to be exact.

Concretely, the check that the composite unit is invertible at a bounded below complex `K`
of injectives uses Mathlib's criterion that the unit of a bounded below right derived
functor is invertible at any complex all of whose terms are injective
(the instance in `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`).
Applied to `G` this is exactly where `F.PreservesInjectiveObjects` enters: the terms of
`F.mapHomotopyCategoryPlus.obj K` are the `F.obj (K.X n)`, injective because `F` preserves
injectives.

## Main definitions

- `CategoryTheory.Functor.rightDerivedFunctorPlusNatTrans` and
  `Functor.rightDerivedFunctorPlusNatIso`: functoriality of the bounded below right derived
  functor in natural transformations of the underived functors.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`: the composition isomorphism
  `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'`: the composition isomorphism
  `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism `F ⋙ G ≅ H`. This is the form in which
  the theorem is usually applied, e.g. for the Leray isomorphism.
- `CategoryTheory.Functor.rightDerivedFunctorPlusIdIso`: the identity isomorphism
  `R⁺(𝟭 C) ≅ 𝟭`, expressing that the identity functor is its own right derived functor.

Both composition isomorphisms are characterized by their compatibility with the units of the
right derived functors, in `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_fac` and
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'_fac`.

Finally, `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_id_comp`,
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_comp_id` and
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` are the unit and associativity
laws relating `rightDerivedFunctorPlusCompIso` and `rightDerivedFunctorPlusIdIso`, and
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'_assoc` is the associativity law for
the primed composition isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Functoriality of the bounded below right derived functor: a natural transformation
`F ⟶ G` of additive functors induces a natural transformation
`R⁺F ⟶ R⁺G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`. -/
noncomputable def rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  rightDerivedNatTrans F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) DerivedCategory.Plus.Qh)

/-- Functoriality of the bounded below right derived functor in natural isomorphisms: an
isomorphism `F ≅ G` of additive functors induces an isomorphism `R⁺F ≅ R⁺G`. -/
noncomputable def rightDerivedFunctorPlusNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) : F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := rightDerivedFunctorPlusNatTrans e.hom
  inv := rightDerivedFunctorPlusNatTrans e.inv
  hom_inv_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]
  inv_hom_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

/-- The natural transformation `Functor.rightDerivedFunctorPlusNatTrans τ` is characterized
by its compatibility with the units of the two right derived functors: on the image of a
bounded below complex it is the levelwise image of `τ`. -/
@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusNatTrans_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatTrans τ).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app K) ≫
        G.rightDerivedFunctorPlusUnith.app K := by
  simp [rightDerivedFunctorPlusNatTrans]

/-- The natural transformation induced on bounded below right derived functors by a natural
isomorphism is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) [IsIso τ] : IsIso (rightDerivedFunctorPlusNatTrans τ) :=
  inferInstanceAs (IsIso (rightDerivedFunctorPlusNatIso (asIso τ)).hom)

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composite unit exhibiting `R⁺F ⋙ R⁺G` as a candidate right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: it is assembled from the units of `R⁺F` and `R⁺G`
and the composition isomorphism of `mapHomotopyCategoryPlus`. -/
noncomputable def rightDerivedFunctorPlusCompUnit :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The composite unit `Functor.rightDerivedFunctorPlusCompUnit` is simply the composite of
the units of `R⁺G` and `R⁺F`: the comparison isomorphism of `mapHomotopyCategoryPlus`
occurring in its definition is the identity. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompUnit_app (K : HomotopyCategory.Plus C) :
    (rightDerivedFunctorPlusCompUnit F G).app K =
      G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
  simp [rightDerivedFunctorPlusCompUnit, mapHomotopyCategoryPlusCompIso_refl_inv_app]

/-- If `F` preserves injective objects, then `R⁺F ⋙ R⁺G`, equipped with the composite unit,
is a right derived functor of `(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: by the injective
right derivability structure it suffices that the composite unit is an isomorphism on
bounded below complexes of injectives, which holds since the unit of `R⁺F` is an
isomorphism there and the unit of `R⁺G` is an isomorphism on their images under `F`, those
being complexes of injectives again. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp [F.PreservesInjectiveObjects] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  set K : HomotopyCategory.Plus C := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁
    with hK
  have hKinj : ∀ n : ℤ, Injective (K.obj.as.X n) := fun n => inferInstance
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnith.app K) := inferInstance
  have hFinj : ∀ n : ℤ, Injective ((F.mapHomotopyCategoryPlus.obj K).obj.as.X n) := fun n =>
    inferInstanceAs (Injective (F.obj (K.obj.as.X n)))
  have h₂ : IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) := by
    have := hFinj
    infer_instance
  dsimp [rightDerivedFunctorPlusCompUnit]
  infer_instance

/-- **Composition of bounded below right derived functors**: for additive functors
`F : C ⥤ D` and `G : D ⥤ E` between abelian categories with enough injectives, where `F`
preserves injective objects, the canonical comparison `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G` is an
isomorphism. -/
noncomputable def rightDerivedFunctorPlusCompIso [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnith (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso` is characterized by
its compatibility with the units: composing the unit of `R⁺(F ⋙ G)` with it gives the
composite unit `Functor.rightDerivedFunctorPlusCompUnit`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso_fac [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlusUnith ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusCompIso F G).hom =
      rightDerivedFunctorPlusCompUnit F G := by
  simp [rightDerivedFunctorPlusCompIso]

/-- The pointwise form of `Functor.rightDerivedFunctorPlusCompIso_fac`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso_fac_app [F.PreservesInjectiveObjects]
    (K : HomotopyCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedFunctorPlusCompUnit F G).app K :=
  NatTrans.congr_app (rightDerivedFunctorPlusCompIso_fac F G) K

/-- The composition isomorphism `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism
`F ⋙ G ≅ H` of additive functors, for `F` preserving injective objects. This is the form in
which the composition theorem is usually applied, e.g. for the Leray isomorphism
`RΓ(Y, R⁺f_* K) ≅ RΓ(X, K)`. -/
noncomputable def rightDerivedFunctorPlusCompIso' {H : C ⥤ E} [H.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso F G).symm ≪≫ rightDerivedFunctorPlusNatIso e

/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso'` attached to an
isomorphism `e : F ⋙ G ≅ H` is characterized by its compatibility with the units: composing
the composite unit with it gives the unit of `R⁺H`, transported along `e`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso'_fac {H : C ⥤ E} [H.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) :
    rightDerivedFunctorPlusCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom) DerivedCategory.Plus.Qh ≫
        H.rightDerivedFunctorPlusUnith := by
  rw [← rightDerivedFunctorPlusCompIso_fac F G, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedFunctorPlusCompIso', Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.Plus.quasiIso C) _

end Composition

section Identity

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]
  [EnoughInjectives C]

/-- The unit exhibiting the identity functor of `DerivedCategory.Plus C` as a right derived
functor of `(𝟭 C).mapHomotopyCategoryPlus ⋙ Qh`. It is an isomorphism: the functor
`(𝟭 C).mapHomotopyCategoryPlus ⋙ Qh` is `Qh` itself, which already inverts the
quasi-isomorphisms. -/
noncomputable def rightDerivedFunctorPlusIdUnit :
    (𝟭 C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ 𝟭 (DerivedCategory.Plus C) :=
  Functor.whiskerRight (mapHomotopyCategoryPlusIdIso C).hom DerivedCategory.Plus.Qh ≫
    DerivedCategory.Plus.Qh.leftUnitor.hom ≫ DerivedCategory.Plus.Qh.rightUnitor.inv

omit [EnoughInjectives C] in
@[simp]
lemma rightDerivedFunctorPlusIdUnit_app (K : HomotopyCategory.Plus C) :
    (rightDerivedFunctorPlusIdUnit C).app K = 𝟙 _ := by
  simp only [rightDerivedFunctorPlusIdUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, comp_id,
    mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  exact (Category.comp_id _).trans (DerivedCategory.Plus.Qh.map_id K)

instance : IsIso (rightDerivedFunctorPlusIdUnit C) := by
  dsimp only [rightDerivedFunctorPlusIdUnit]
  infer_instance

instance isRightDerivedFunctor_id_rightDerivedFunctorPlusIdUnit :
    (𝟭 (DerivedCategory.Plus C)).IsRightDerivedFunctor (rightDerivedFunctorPlusIdUnit C)
      (HomotopyCategory.Plus.quasiIso C) :=
  isRightDerivedFunctor_of_inverts _ _ (asIso (rightDerivedFunctorPlusIdUnit C)).symm

/-- **The identity functor is its own bounded below right derived functor**: the canonical
comparison `R⁺(𝟭 C) ≅ 𝟭` is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusIdIso :
    (𝟭 C).rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus C) :=
  rightDerivedUnique (𝟭 C).rightDerivedFunctorPlus (𝟭 (DerivedCategory.Plus C))
    (𝟭 C).rightDerivedFunctorPlusUnith (rightDerivedFunctorPlusIdUnit C)
    (HomotopyCategory.Plus.quasiIso C)

/-- The characterization of `Functor.rightDerivedFunctorPlusIdIso`: it transforms the unit of
`R⁺(𝟭 C)` into the identity, up to the unitors. -/
@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso :
    (𝟭 C).rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusIdIso C).hom =
      rightDerivedFunctorPlusIdUnit C := by
  simp [rightDerivedFunctorPlusIdIso]

/-- The pointwise form of
`Functor.rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso`: the identity
isomorphism `Functor.rightDerivedFunctorPlusIdIso` turns the unit of `R⁺(𝟭 C)` into
`Functor.mapHomotopyCategoryPlusIdIso`. -/
@[reassoc]
lemma rightDerivedFunctorPlusIdIso_fac_app (K : HomotopyCategory.Plus C) :
    (𝟭 C).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) := by
  have := congr_app (rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso C) K
  simpa [rightDerivedFunctorPlusIdUnit,
    -rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso] using this

end Identity

section Coherence

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {E' : Type*}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
  [EnoughInjectives C]

/-- The left unit law for `Functor.rightDerivedFunctorPlusCompIso`: composing with the
identity isomorphism `Functor.rightDerivedFunctorPlusIdIso` in the first variable gives the
identity. -/
lemma rightDerivedFunctorPlusCompIso_id_comp (G : C ⥤ D) [G.Additive] :
    (rightDerivedFunctorPlusCompIso (𝟭 C) G).hom ≫
        Functor.whiskerRight (rightDerivedFunctorPlusIdIso C).hom G.rightDerivedFunctorPlus =
      𝟙 G.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext (𝟭 C ⋙ G).rightDerivedFunctorPlus
    (𝟭 C ⋙ G).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app]
  rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app,
    rightDerivedFunctorPlusCompUnit_app, Category.assoc, ← Functor.map_comp,
    rightDerivedFunctorPlusIdIso_fac_app, mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  have h : G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (𝟙 K)) =
      𝟙 (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
    rw [DerivedCategory.Plus.Qh.map_id]
    exact G.rightDerivedFunctorPlus.map_id _
  rw [h]
  exact (Category.comp_id _).trans (Category.comp_id _).symm

/-- The right unit law for `Functor.rightDerivedFunctorPlusCompIso`: composing with the
identity isomorphism `Functor.rightDerivedFunctorPlusIdIso` in the second variable gives the
identity. -/
lemma rightDerivedFunctorPlusCompIso_comp_id [EnoughInjectives D] (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] :
    (rightDerivedFunctorPlusCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso D).hom =
      𝟙 F.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext (F ⋙ 𝟭 D).rightDerivedFunctorPlus
    (F ⋙ 𝟭 D).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (𝟭 D).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      (rightDerivedFunctorPlusIdIso D).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (rightDerivedFunctorPlusIdIso D).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        F.rightDerivedFunctorPlusUnith.app K :=
    (rightDerivedFunctorPlusIdIso D).hom.naturality _
  rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app,
    rightDerivedFunctorPlusCompUnit_app, Category.assoc, hnat, ← Category.assoc,
    rightDerivedFunctorPlusIdIso_fac_app, mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  have h : DerivedCategory.Plus.Qh.map (𝟙 (F.mapHomotopyCategoryPlus.obj K)) =
      𝟙 (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) :=
    DerivedCategory.Plus.Qh.map_id _
  rw [h]
  exact (Category.id_comp _).trans (Category.comp_id _).symm


/-- The associativity law for `Functor.rightDerivedFunctorPlusCompIso`: the two ways of
comparing `R⁺(F ⋙ G ⋙ H)` with `R⁺F ⋙ R⁺G ⋙ R⁺H` agree. -/
lemma rightDerivedFunctorPlusCompIso_assoc [EnoughInjectives D] [EnoughInjectives E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] :
    (rightDerivedFunctorPlusCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIso G H).hom =
      (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (rightDerivedFunctorPlusCompIso F G).hom
          H.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext (F ⋙ G ⋙ H).rightDerivedFunctorPlus
    (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (G ⋙ H).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      (rightDerivedFunctorPlusCompIso G H).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (rightDerivedFunctorPlusCompIso G H).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlus.map
          (F.rightDerivedFunctorPlusUnith.app K)) :=
    (rightDerivedFunctorPlusCompIso G H).hom.naturality _
  have facR : (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedFunctorPlusCompUnit (F ⋙ G) H).app K :=
    rightDerivedFunctorPlusCompIso_fac_app (F ⋙ G) H K
  have unitR : (rightDerivedFunctorPlusCompUnit (F ⋙ G) H).app K =
      H.rightDerivedFunctorPlusUnith.app (G.mapHomotopyCategoryPlus.obj
          (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map ((F ⋙ G).rightDerivedFunctorPlusUnith.app K) :=
    rightDerivedFunctorPlusCompUnit_app (F ⋙ G) H K
  trans H.rightDerivedFunctorPlusUnith.app
      (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
    H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusUnith.app
      (F.mapHomotopyCategoryPlus.obj K)) ≫
    H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusUnith.app K))
  · rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app,
      rightDerivedFunctorPlusCompUnit_app, Category.assoc, hnat, ← Category.assoc,
      rightDerivedFunctorPlusCompIso_fac_app, rightDerivedFunctorPlusCompUnit_app,
      Category.assoc]
  · symm
    rw [← Category.assoc, facR, unitR, Category.assoc, ← Functor.map_comp,
      rightDerivedFunctorPlusCompIso_fac_app, rightDerivedFunctorPlusCompUnit_app,
      Functor.map_comp]

/-- **The associativity law for `Functor.rightDerivedFunctorPlusCompIso'`**: given
isomorphisms `e₁ : F ⋙ G ≅ FG`, `e₂ : G ⋙ H ≅ GH`, `e₃ : FG ⋙ H ≅ FGH` and
`e₄ : F ⋙ GH ≅ FGH` compatible in the evident sense, the two ways of comparing
`R⁺F ⋙ R⁺G ⋙ R⁺H` with `R⁺FGH` agree. -/
lemma rightDerivedFunctorPlusCompIso'_assoc [EnoughInjectives D] [EnoughInjectives E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') (FG : C ⥤ E) (GH : D ⥤ E') (FGH : C ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [FGH.Additive]
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
    [FG.PreservesInjectiveObjects]
    (e₁ : F ⋙ G ≅ FG) (e₂ : G ⋙ H ≅ GH) (e₃ : FG ⋙ H ≅ FGH) (e₄ : F ⋙ GH ≅ FGH)
    (hcompat : whiskerRight e₁.hom H ≫ e₃.hom = whiskerLeft F e₂.hom ≫ e₄.hom) :
    whiskerRight (rightDerivedFunctorPlusCompIso' F G e₁).hom H.rightDerivedFunctorPlus ≫
        (rightDerivedFunctorPlusCompIso' FG H e₃).hom =
      whiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIso' G H e₂).hom ≫
        (rightDerivedFunctorPlusCompIso' F GH e₄).hom := by
  rw [← cancel_epi (whiskerRight (rightDerivedFunctorPlusCompIso F G).hom
    H.rightDerivedFunctorPlus)]
  refine rightDerived_ext ((F ⋙ G).rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus)
    (rightDerivedFunctorPlusCompUnit (F ⋙ G) H) (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, comp_obj]
  have hCI'₁ : (rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      (rightDerivedFunctorPlusCompIso' F G e₁).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedFunctorPlusNatTrans e₁.hom).app (DerivedCategory.Plus.Qh.obj K) := by
    have hd : (rightDerivedFunctorPlusCompIso' F G e₁).hom =
        (rightDerivedFunctorPlusCompIso F G).inv ≫
          rightDerivedFunctorPlusNatTrans e₁.hom := rfl
    rw [hd, NatTrans.comp_app, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hunit := rightDerivedFunctorPlusCompUnit_app (F ⋙ G) H K
  have hfac3 : (rightDerivedFunctorPlusCompUnit FG H).app K ≫
      (rightDerivedFunctorPlusCompIso' FG H e₃).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e₃.hom).app K) ≫
        FGH.rightDerivedFunctorPlusUnith.app K :=
    NatTrans.congr_app (rightDerivedFunctorPlusCompIso'_fac FG H e₃) K
  have hfac2 : (rightDerivedFunctorPlusCompUnit G H).app (F.mapHomotopyCategoryPlus.obj K) ≫
      (rightDerivedFunctorPlusCompIso' G H e₂).hom.app
        (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e₂.hom).app
          (F.mapHomotopyCategoryPlus.obj K)) ≫
        GH.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) :=
    NatTrans.congr_app (rightDerivedFunctorPlusCompIso'_fac G H e₂)
      (F.mapHomotopyCategoryPlus.obj K)
  have hfac4 : (rightDerivedFunctorPlusCompUnit F GH).app K ≫
      (rightDerivedFunctorPlusCompIso' F GH e₄).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e₄.hom).app K) ≫
        FGH.rightDerivedFunctorPlusUnith.app K :=
    NatTrans.congr_app (rightDerivedFunctorPlusCompIso'_fac F GH e₄) K
  trans DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
      (whiskerRight e₁.hom H ≫ e₃.hom)).app K) ≫ FGH.rightDerivedFunctorPlusUnith.app K
  · have hnatH := H.rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus e₁.hom).app K)
    simp only [comp_obj, comp_map] at hnatH
    have hbridge : H.mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus e₁.hom).app K) =
        (NatTrans.mapHomotopyCategoryPlus (whiskerRight e₁.hom H)).app K := rfl
    rw [← Functor.map_comp_assoc, hCI'₁, hunit, Category.assoc,
      ← Functor.map_comp_assoc, rightDerivedFunctorPlusNatTrans_app, Functor.map_comp,
      Category.assoc, ← reassoc_of% hnatH, ← rightDerivedFunctorPlusCompUnit_app_assoc FG H K,
      hfac3, hbridge,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp]
  · rw [hcompat]
    have hnatCI2 := (rightDerivedFunctorPlusCompIso' G H e₂).hom.naturality
      (F.rightDerivedFunctorPlusUnith.app K)
    simp only [comp_obj, comp_map] at hnatCI2
    have hbridge2 : (NatTrans.mapHomotopyCategoryPlus e₂.hom).app
        (F.mapHomotopyCategoryPlus.obj K) =
        (NatTrans.mapHomotopyCategoryPlus (whiskerLeft F e₂.hom)).app K := rfl
    have hGH : H.rightDerivedFunctorPlusUnith.app ((F ⋙ G).mapHomotopyCategoryPlus.obj K) ≫
        H.rightDerivedFunctorPlus.map
          (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) =
        (rightDerivedFunctorPlusCompUnit G H).app (F.mapHomotopyCategoryPlus.obj K) :=
      (rightDerivedFunctorPlusCompUnit_app G H (F.mapHomotopyCategoryPlus.obj K)).symm
    rw [hunit, Category.assoc, ← Functor.map_comp_assoc,
      rightDerivedFunctorPlusCompIso_fac_app, rightDerivedFunctorPlusCompUnit_app,
      Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hGH, reassoc_of% hnatCI2, reassoc_of% hfac2,
      ← rightDerivedFunctorPlusCompUnit_app_assoc F GH K,
      hfac4, hbridge2,
      ← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

end Coherence

end Functor

end CategoryTheory
