/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# Ring-sheaf lift of a finite-limit-preserving inverse image

Source: Stacks Project, Sites, Tag 00YV, the discussion before the proposition and
its proof for rings as sextuples (auxiliary; not a blueprint node).

The four helper maps are the actual sectionwise operations of a ring sheaf, regarded
as maps of sheaves of sets. The theorem records their transport by the canonical
product and terminal comparisons and the compatibility of the lifted adjunction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory

/-- Addition of a ring sheaf as a map of sheaves of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(auxiliary; not a blueprint node). -/
def ringSheafAdd {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (sheafCompose J (forget CommRingCat.{u})).obj R ⊗
      (sheafCompose J (forget CommRingCat.{u})).obj R ⟶
        (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : R.obj.obj U × R.obj.obj U ↦ x.1 + x.2)
     naturality := by
       intro U V f
       ext x
       change R.obj.obj U × R.obj.obj U at x
       change (R.obj.map f).hom x.1 + (R.obj.map f).hom x.2 =
         (R.obj.map f).hom (x.1 + x.2)
       exact (map_add _ _ _).symm }⟩

/-- Multiplication of a ring sheaf as a map of sheaves of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(auxiliary; not a blueprint node). -/
def ringSheafMul {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (sheafCompose J (forget CommRingCat.{u})).obj R ⊗
      (sheafCompose J (forget CommRingCat.{u})).obj R ⟶
        (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : R.obj.obj U × R.obj.obj U ↦ x.1 * x.2)
     naturality := by
       intro U V f
       ext x
       change R.obj.obj U × R.obj.obj U at x
       change (R.obj.map f).hom x.1 * (R.obj.map f).hom x.2 =
         (R.obj.map f).hom (x.1 * x.2)
       exact (map_mul _ _ _).symm }⟩

/-- Zero of a ring sheaf as a map from the terminal sheaf of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(auxiliary; not a blueprint node). -/
def ringSheafZero {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change (0 : R.obj.obj V) = (R.obj.map f).hom 0
       exact (map_zero _).symm }⟩

/-- One of a ring sheaf as a map from the terminal sheaf of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(auxiliary; not a blueprint node). -/
def ringSheafOne {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change (1 : R.obj.obj V) = (R.obj.map f).hom 1
       exact (map_one _).symm }⟩

private theorem ringBinary_cast
    {A : Type*} [Category A] [CartesianMonoidalCategory A] [BraidedCategory A]
    (op : ∀ X : CommRingObjCat A, X.X ⊗ X.X ⟶ X.X)
    {X Y : CommRingObjCat A} (h : X = Y) :
    op X ≫ eqToHom (congrArg CommRingObjCat.X h) =
      (eqToHom (congrArg CommRingObjCat.X h) ⊗ₘ
        eqToHom (congrArg CommRingObjCat.X h)) ≫ op Y := by
  subst h
  simp

private theorem ringConstant_cast
    {A : Type*} [Category A] [CartesianMonoidalCategory A] [BraidedCategory A]
    (op : ∀ X : CommRingObjCat A, 𝟙_ A ⟶ X.X)
    {X Y : CommRingObjCat A} (h : X = Y) :
    op X ≫ eqToHom (congrArg CommRingObjCat.X h) = op Y := by
  subst h
  simp

private theorem binaryTransport
    {A B : Type*} [Category A] [CartesianMonoidalCategory A]
    [Category B] [CartesianMonoidalCategory B]
    (L : A ⥤ B) [PreservesFiniteProducts L]
    {X X' : A} {Y Y' : B} (c : X' = X) (d : Y = Y') (r : Y' = L.obj X')
    (e : L.obj X = Y)
    (s : X ⊗ X ⟶ X) (t : X' ⊗ X' ⟶ X') (u : Y' ⊗ Y' ⟶ Y')
    (v : Y ⊗ Y ⟶ Y)
    (hs : t ≫ eqToHom c = (eqToHom c ⊗ₘ eqToHom c) ≫ s)
    (ht : v ≫ eqToHom d = (eqToHom d ⊗ₘ eqToHom d) ≫ u)
    (hl : u ≫ eqToHom r = (eqToHom r ⊗ₘ eqToHom r) ≫
      (prodComparisonIso L X' X').inv ≫ L.map t) :
    L.map s ≫ eqToHom e = (prodComparisonIso L X X).hom ≫
      (eqToHom e ⊗ₘ eqToHom e) ≫ v := by
  subst X'
  subst Y
  subst Y'
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp,
    Category.comp_id] at hs ht hl ⊢
  rw [ht, hl, hs]
  exact (Iso.hom_inv_id_assoc (prodComparisonIso L X X) _).symm

private theorem constantTransport
    {A B : Type*} [Category A] [CartesianMonoidalCategory A]
    [Category B] [CartesianMonoidalCategory B]
    (L : A ⥤ B) [PreservesFiniteProducts L]
    {X X' : A} {Y Y' : B} (c : X' = X) (d : Y = Y') (r : Y' = L.obj X')
    (e : L.obj X = Y)
    (s : 𝟙_ A ⟶ X) (t : 𝟙_ A ⟶ X') (u : 𝟙_ B ⟶ Y') (v : 𝟙_ B ⟶ Y)
    (hs : t ≫ eqToHom c = s)
    (ht : v ≫ eqToHom d = u)
    (hl : u ≫ eqToHom r = (preservesTerminalIso L).inv ≫ L.map t) :
    L.map s ≫ eqToHom e = (preservesTerminalIso L).hom ≫ v := by
  subst X'
  subst Y
  subst Y'
  simp only [eqToHom_refl, Category.comp_id] at hs ht hl ⊢
  rw [ht, hl, hs]
  exact (Iso.hom_inv_id_assoc (preservesTerminalIso L) _).symm

private theorem homEquivCast
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {V : B ⥤ A} (adj : L ⊣ V)
    {X' X : A} {Y' Y : B} (c : X' = X) (d : Y' = Y) (f : L.obj X' ⟶ Y') :
    eqToHom c.symm ≫ adj.homEquiv X' Y' f ≫ V.map (eqToHom d) =
      adj.homEquiv X Y (L.map (eqToHom c.symm) ≫ f ≫ eqToHom d) := by
  subst X'
  subst Y'
  simp

/-- A finite-limit-preserving left adjoint on set sheaves lifts to commutative ring
sheaves, naturally on underlying sheaves and compatibly with operations and adjunction.
Source: Stacks Project, Sites, Tag 00YV, discussion before the proposition and proof
for rings as sextuples (auxiliary; not a blueprint node).

The components of `e` are the stated `e_R`; its naturality is exactly the equation
for every ring-sheaf morphism. The comparison `v` identifies the underlying right
adjoint, so that the final equation compares hom-equivalences in the same hom-set.
The operation equations have domain `L (|R| × |R|)` or `L (*)`, respectively, and
are equivalent to transporting by the inverses of the canonical comparisons.

Proof:
1. Use `sheaves_algebraicStructures_objects`
   (situation-conventions) on each site to identify ring
   sheaves with internal commutative ring objects, compatibly with forgetting.
2. Finite-limit preservation implies preservation of binary products and the terminal
   object. Apply `Adjunction.liftsGroupRingObjects`
   (lem-weil-pbc-adjunction-lifts-group-ring-objects) to the given adjunction. Its
   ring branch supplies both functors, their adjunction, underlying comparisons,
   and the transport equations for all ring operations.
3. Conjugate both functors and the adjunction by the identifications from step 1.
   The underlying comparisons give `e` and `v`; their naturality gives the asserted
   equation on ring morphisms. The sectionwise operations in step 1 convert the
   operation equations from step 2 to the four displayed equations here.
4. Transport the hom-equivalence clause from step 2 through the same identifications.
   This gives the last equation, hence exactly the original set-sheaf hom-equivalence
   after forgetting rings and applying the underlying comparisons. -/
theorem inverseImage_ring_functor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (rings : Sheaf J CommRingCat.{u} ⥤ Sheaf K CommRingCat.{u})
      (Vrings : Sheaf K CommRingCat.{u} ⥤ Sheaf J CommRingCat.{u})
      (a : rings ⊣ Vrings)
      (e : sheafCompose J (forget CommRingCat.{u}) ⋙ L ≅
        rings ⋙ sheafCompose K (forget CommRingCat.{u}))
      (v : Vrings ⋙ sheafCompose J (forget CommRingCat.{u}) ≅
        sheafCompose K (forget CommRingCat.{u}) ⋙ V),
      (∀ R : Sheaf J CommRingCat.{u},
        L.map (ringSheafAdd R) ≫ (e.app R).hom =
          (prodComparisonIso L _ _).hom ≫ ((e.app R).hom ⊗ₘ (e.app R).hom) ≫
            ringSheafAdd (rings.obj R) ∧
        L.map (ringSheafMul R) ≫ (e.app R).hom =
          (prodComparisonIso L _ _).hom ≫ ((e.app R).hom ⊗ₘ (e.app R).hom) ≫
            ringSheafMul (rings.obj R) ∧
        L.map (ringSheafZero R) ≫ (e.app R).hom =
          (preservesTerminalIso L).hom ≫ ringSheafZero (rings.obj R) ∧
        L.map (ringSheafOne R) ≫ (e.app R).hom =
          (preservesTerminalIso L).hom ≫ ringSheafOne (rings.obj R)) ∧
      (∀ (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
        (f : rings.obj R ⟶ S),
        (sheafCompose J (forget CommRingCat.{u})).map (a.homEquiv R S f) ≫
            (v.app S).hom =
          adj.homEquiv ((sheafCompose J (forget CommRingCat.{u})).obj R)
            ((sheafCompose K (forget CommRingCat.{u})).obj S)
            ((e.app R).hom ≫ (sheafCompose K (forget CommRingCat.{u})).map f)) := by
  obtain ⟨FJ, GJ, hFJ, hGJ, hFJGJ, hGJFJ, opsJ, _⟩ :=
    (sheaves_algebraicStructures_objects.{u, u, u} J).2.2.2
  obtain ⟨FK, GK, hFK, hGK, hFKGK, hGKFK, opsK, _⟩ :=
    (sheaves_algebraicStructures_objects.{u, u, u} K).2.2.2
  obtain ⟨_, _, LF, RF, hLF, hRF, a, hops, _, hhom, _⟩ :=
    adj.liftsGroupRingObjects
  let eJ : Sheaf J CommRingCat.{u} ≌ CommRingObjCat (Sheaf J (Type u)) :=
    ⟨FJ, GJ, eqToIso hFJGJ.symm, eqToIso hGJFJ, by
      intro X
      simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans,
        eqToHom_refl]⟩
  let eK : Sheaf K CommRingCat.{u} ≌ CommRingObjCat (Sheaf K (Type u)) :=
    ⟨FK, GK, eqToIso hFKGK.symm, eqToIso hGKFK, by
      intro X
      simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans,
        eqToHom_refl]⟩
  let rings := (FJ ⋙ LF) ⋙ GK
  let Vrings := (FK ⋙ RF) ⋙ GJ
  let ar : rings ⊣ Vrings :=
    ((eJ.toAdjunction.comp a).comp eK.symm.toAdjunction).ofNatIsoRight
      (Functor.associator FK RF GJ).symm
  have he : rings ⋙ sheafCompose K (forget CommRingCat.{u}) =
      sheafCompose J (forget CommRingCat.{u}) ⋙ L := by
    dsimp [rings]
    rw [Functor.assoc, hGK, Functor.assoc, hLF, ← Functor.assoc, hFJ]
  have hv : Vrings ⋙ sheafCompose J (forget CommRingCat.{u}) =
      sheafCompose K (forget CommRingCat.{u}) ⋙ V := by
    dsimp [Vrings]
    rw [Functor.assoc, hGJ, Functor.assoc, hRF, ← Functor.assoc, hFK]
  let e := (eqToIso he).symm
  let v := eqToIso hv
  have addJ (R : Sheaf J CommRingCat.{u}) :
      AddMonObj.add (X := (FJ.obj R).X) ≫ (eqToIso hFJ).hom.app R =
        ((eqToIso hFJ).hom.app R ⊗ₘ (eqToIso hFJ).hom.app R) ≫ ringSheafAdd R := by
    ext U x
    exact (opsJ R U).1 x.1 x.2
  have addK (R : Sheaf K CommRingCat.{u}) :
      AddMonObj.add (X := (FK.obj R).X) ≫ (eqToIso hFK).hom.app R =
        ((eqToIso hFK).hom.app R ⊗ₘ (eqToIso hFK).hom.app R) ≫ ringSheafAdd R := by
    ext U x
    exact (opsK R U).1 x.1 x.2
  have mulJ (R : Sheaf J CommRingCat.{u}) :
      MonObj.mul (X := (FJ.obj R).X) ≫ (eqToIso hFJ).hom.app R =
        ((eqToIso hFJ).hom.app R ⊗ₘ (eqToIso hFJ).hom.app R) ≫
          ringSheafMul R := by
    ext U x
    exact (opsJ R U).2.2.2.1 x.1 x.2
  have mulK (R : Sheaf K CommRingCat.{u}) :
      MonObj.mul (X := (FK.obj R).X) ≫ (eqToIso hFK).hom.app R =
        ((eqToIso hFK).hom.app R ⊗ₘ (eqToIso hFK).hom.app R) ≫
          ringSheafMul R := by
    ext U x
    exact (opsK R U).2.2.2.1 x.1 x.2
  have zeroJ (R : Sheaf J CommRingCat.{u}) :
      AddMonObj.zero (X := (FJ.obj R).X) ≫ (eqToIso hFJ).hom.app R =
        ringSheafZero R := by
    ext U x
    exact (opsJ R U).2.1 x
  have zeroK (R : Sheaf K CommRingCat.{u}) :
      AddMonObj.zero (X := (FK.obj R).X) ≫ (eqToIso hFK).hom.app R =
        ringSheafZero R := by
    ext U x
    exact (opsK R U).2.1 x
  have oneJ (R : Sheaf J CommRingCat.{u}) :
      MonObj.one (X := (FJ.obj R).X) ≫ (eqToIso hFJ).hom.app R =
        ringSheafOne R := by
    ext U x
    exact (opsJ R U).2.2.2.2 x
  have oneK (R : Sheaf K CommRingCat.{u}) :
      MonObj.one (X := (FK.obj R).X) ≫ (eqToIso hFK).hom.app R =
        ringSheafOne R := by
    ext U x
    exact (opsK R U).2.2.2.2 x
  have addGK (X : CommRingObjCat (Sheaf K (Type u))) :
      ringSheafAdd (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        ((eqToIso hGK).hom.app X ⊗ₘ (eqToIso hGK).hom.app X) ≫
          AddMonObj.add (X := X.X) := by
    apply (cancel_epi ((eqToIso hFK).hom.app (GK.obj X) ⊗ₘ
      (eqToIso hFK).hom.app (GK.obj X))).1
    rw [← Category.assoc, ← addK, Category.assoc]
    have hc : (eqToIso hFK).hom.app (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        eqToHom (congrArg CommRingObjCat.X (Functor.congr_obj hGKFK X)) := by
      simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
    rw [hc]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hc]
    exact ringBinary_cast (fun Y ↦ AddMonObj.add (X := Y.X))
      (Functor.congr_obj hGKFK X)
  have mulGK (X : CommRingObjCat (Sheaf K (Type u))) :
      ringSheafMul (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        ((eqToIso hGK).hom.app X ⊗ₘ (eqToIso hGK).hom.app X) ≫
          MonObj.mul (X := X.X) := by
    apply (cancel_epi ((eqToIso hFK).hom.app (GK.obj X) ⊗ₘ
      (eqToIso hFK).hom.app (GK.obj X))).1
    rw [← Category.assoc, ← mulK, Category.assoc]
    have hc : (eqToIso hFK).hom.app (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        eqToHom (congrArg CommRingObjCat.X (Functor.congr_obj hGKFK X)) := by
      simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
    rw [hc]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hc]
    exact ringBinary_cast (fun Y ↦ MonObj.mul (X := Y.X))
      (Functor.congr_obj hGKFK X)
  have zeroGK (X : CommRingObjCat (Sheaf K (Type u))) :
      ringSheafZero (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        AddMonObj.zero (X := X.X) := by
    have hc : (eqToIso hFK).hom.app (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        eqToHom (congrArg CommRingObjCat.X (Functor.congr_obj hGKFK X)) := by
      simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
    rw [← zeroK, Category.assoc, hc]
    exact ringConstant_cast (fun Y ↦ AddMonObj.zero (X := Y.X)) (Functor.congr_obj hGKFK X)
  have oneGK (X : CommRingObjCat (Sheaf K (Type u))) :
      ringSheafOne (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        MonObj.one (X := X.X) := by
    have hc : (eqToIso hFK).hom.app (GK.obj X) ≫ (eqToIso hGK).hom.app X =
        eqToHom (congrArg CommRingObjCat.X (Functor.congr_obj hGKFK X)) := by
      simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
    rw [← oneK, Category.assoc, hc]
    exact ringConstant_cast (fun Y ↦ MonObj.one (X := Y.X)) (Functor.congr_obj hGKFK X)
  refine ⟨rings, Vrings, ar, e, v, ?_, ?_⟩
  · intro R
    have hc : (FJ.obj R).X = (sheafCompose J (forget CommRingCat.{u})).obj R :=
      Functor.congr_obj hFJ R
    have hd : (sheafCompose K (forget CommRingCat.{u})).obj (rings.obj R) =
        (LF.obj (FJ.obj R)).X := Functor.congr_obj hGK (LF.obj (FJ.obj R))
    have hr : (LF.obj (FJ.obj R)).X = L.obj (FJ.obj R).X :=
      Functor.congr_obj hLF (FJ.obj R)
    have he' : L.obj ((sheafCompose J (forget CommRingCat.{u})).obj R) =
        (sheafCompose K (forget CommRingCat.{u})).obj (rings.obj R) :=
      Functor.congr_obj he.symm R
    simp only [Iso.app_hom, e, Iso.symm_hom, eqToIso.inv, eqToHom_app]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply binaryTransport L hc hd hr he' (ringSheafAdd R)
        (AddMonObj.add (X := (FJ.obj R).X))
        (AddMonObj.add (X := (LF.obj (FJ.obj R)).X))
        (ringSheafAdd (rings.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using addJ R
      · simpa only [rings, Functor.comp_obj, eqToIso.hom, eqToHom_app] using
          addGK (LF.obj (FJ.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using (hops (FJ.obj R)).1
    · apply binaryTransport L hc hd hr he' (ringSheafMul R)
        (MonObj.mul (X := (FJ.obj R).X))
        (MonObj.mul (X := (LF.obj (FJ.obj R)).X))
        (ringSheafMul (rings.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using mulJ R
      · simpa only [rings, Functor.comp_obj, eqToIso.hom, eqToHom_app] using
          mulGK (LF.obj (FJ.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using (hops (FJ.obj R)).2.2.2.1
    · apply constantTransport L hc hd hr he' (ringSheafZero R)
        (AddMonObj.zero (X := (FJ.obj R).X))
        (AddMonObj.zero (X := (LF.obj (FJ.obj R)).X))
        (ringSheafZero (rings.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using zeroJ R
      · simpa only [rings, Functor.comp_obj, eqToIso.hom, eqToHom_app] using
          zeroGK (LF.obj (FJ.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using (hops (FJ.obj R)).2.1
    · apply constantTransport L hc hd hr he' (ringSheafOne R)
        (MonObj.one (X := (FJ.obj R).X))
        (MonObj.one (X := (LF.obj (FJ.obj R)).X))
        (ringSheafOne (rings.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using oneJ R
      · simpa only [rings, Functor.comp_obj, eqToIso.hom, eqToHom_app] using
          oneGK (LF.obj (FJ.obj R))
      · simpa only [eqToIso.hom, eqToHom_app] using (hops (FJ.obj R)).2.2.2.2
  · intro R S f
    let g : LF.obj (FJ.obj R) ⟶ FK.obj S :=
      (eqToIso hGKFK).inv.app (LF.obj (FJ.obj R)) ≫ FK.map f
    have har : ar.homEquiv R S f =
        (eqToIso hFJGJ.symm).hom.app R ≫
          GJ.map (a.homEquiv (FJ.obj R) (FK.obj S) g) := by
      dsimp only [ar]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply]
      simp only [Adjunction.comp_homEquiv]
      simp [Adjunction.homEquiv_unit, eJ, eK, Equivalence.symm,
        Equivalence.toAdjunction, Equivalence.unit, g, Vrings]
      simp [Adjunction.homEquiv, Functor.map_comp]
    have hvS : v.hom.app S =
        (eqToIso hGJ).hom.app (RF.obj (FK.obj S)) ≫
          (eqToIso hRF).hom.app (FK.obj S) ≫ V.map ((eqToIso hFK).hom.app S) := by
      simp only [v, eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
    have hstart :
        (sheafCompose J (forget CommRingCat.{u})).map
            ((eqToIso hFJGJ.symm).hom.app R) ≫ (eqToIso hGJ).hom.app (FJ.obj R) =
          (eqToIso hFJ).inv.app R := by
      simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
    have hin : L.map ((eqToIso hFJ).inv.app R) ≫
        ((eqToIso hLF).inv.app (FJ.obj R) ≫
          (CommRingObjCat.forget (Sheaf K (Type u))).map g) ≫
            (eqToIso hFK).hom.app S =
        e.hom.app R ≫ (sheafCompose K (forget CommRingCat.{u})).map f := by
      dsimp only [g]
      rw [Functor.map_comp]
      simp only [Category.assoc]
      have hn := (eqToIso hFK).hom.naturality f
      dsimp only [Functor.comp_map] at hn
      rw [hn]
      simp only [e, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_app,
        eqToHom_map, eqToHom_trans_assoc]
    calc
      _ = (eqToIso hFJ).inv.app R ≫
          ((CommRingObjCat.forget (Sheaf J (Type u))).map
            (a.homEquiv (FJ.obj R) (FK.obj S) g) ≫
              (eqToIso hRF).hom.app (FK.obj S)) ≫
                V.map ((eqToIso hFK).hom.app S) := by
        rw [har, Functor.map_comp]
        simp only [Iso.app_hom]
        rw [hvS]
        simp only [Category.assoc]
        have hn := (eqToIso hGJ).hom.naturality
          (a.homEquiv (FJ.obj R) (FK.obj S) g)
        dsimp only [Functor.comp_map] at hn
        rw [reassoc_of% hn]
        rw [← Category.assoc, hstart]
      _ = (eqToIso hFJ).inv.app R ≫
          adj.homEquiv (FJ.obj R).X (FK.obj S).X
            ((eqToIso hLF).inv.app (FJ.obj R) ≫
              (CommRingObjCat.forget (Sheaf K (Type u))).map g) ≫
                V.map ((eqToIso hFK).hom.app S) := by
        rw [hhom]
      _ = adj.homEquiv _ _
          (L.map ((eqToIso hFJ).inv.app R) ≫
            ((eqToIso hLF).inv.app (FJ.obj R) ≫
              (CommRingObjCat.forget (Sheaf K (Type u))).map g) ≫
                (eqToIso hFK).hom.app S) := by
        have hc : (FJ.obj R).X = (sheafCompose J (forget CommRingCat.{u})).obj R :=
          Functor.congr_obj hFJ R
        have hd : (FK.obj S).X = (sheafCompose K (forget CommRingCat.{u})).obj S :=
          Functor.congr_obj hFK S
        simpa only [eqToIso.inv, eqToIso.hom, eqToHom_app, Functor.comp_obj,
          CommRingObjCat.forget_obj] using homEquivCast adj hc hd
            ((eqToIso hLF).inv.app (FJ.obj R) ≫
              (CommRingObjCat.forget (Sheaf K (Type u))).map g)
      _ = _ := by rw [hin]; rfl

end CategoryTheory
