/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.R.RHomInjectiveCocycleFamily

/-!
# Extension from injective complexes to `D+`

The transport of compatible cocycle maps through injective resolutions is
isolated from the construction on injective complexes.
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- A compatible normalized family on injective complexes extends to all objects
of the bounded-below derived category.
Source: Stacks Tags 06XR (1) and 070I.
Proof: a bounded-below injective complex is K-injective, so every derived
morphism between two such complexes lifts to a chain map. The compatibility
field therefore applies to every derived morphism between injective models.
Choose a model `QI ≅ X` for each object and conjugate its additive comparison
by this isomorphism, using the induced cohomology map on the source and shifted
postcomposition on the target. Compatibility applied to the conjugate of a
morphism `X ⟶ Y` proves naturality. Applied to the model isomorphism of `QJ`,
it identifies the extension with the original comparison on every injective
complex `J`; the inverse isomorphisms cancel on both sides.
(blueprint: lem-sc-p1-rhom-natural-cocycle-map-extension)
-/
theorem extend_rhom_injective_cocycle_family
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}]
    {M : C} (F : RhomInjectiveCocycleFamily M) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∃ τ : ∀ (X : DerivedCategory.Plus C) (n : ℤ),
        (H n).obj (RV.obj X) →+ (S ⟶ X.obj⟦n⟧),
      (∀ (X Y : DerivedCategory.Plus C) (g : X ⟶ Y) (n : ℤ)
          (a : (H n).obj (RV.obj X)),
        τ Y n ((H n).map (RV.map g) a) =
          τ X n a ≫ ((DerivedCategory.Plus.ι (C := C)).map g)⟦n⟧') ∧
      (∀ (I : CochainComplex.Plus C) (hi : ∀ k : ℤ, Injective (I.obj.X k))
          (n : ℤ) (a : (H n).obj (RV.obj ((DerivedCategory.Plus.Q (C := C)).obj I))),
        τ ((DerivedCategory.Plus.Q (C := C)).obj I) n a = F.map I hi n a) := by
  classical
  dsimp only
  let V := preadditiveCoyoneda.obj (op M)
  let RV := V.rightDerivedFunctorPlus
  let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
  let S := (DerivedCategory.singleFunctor C 0).obj M
  let Q := DerivedCategory.Plus.Q (C := C)
  let U := DerivedCategory.Plus.ι (C := C)
  have hnI (I J : CochainComplex.Plus C)
      (hi : ∀ k : ℤ, Injective (I.obj.X k))
      (hj : ∀ k : ℤ, Injective (J.obj.X k))
      (g : Q.obj I ⟶ Q.obj J) (n : ℤ)
      (a : (H n).obj (RV.obj (Q.obj I))) :
      F.map J hj n ((H n).map (RV.map g) a) =
        F.map I hi n a ≫ (U.map g)⟦n⟧' := by
    let := hj
    obtain ⟨m, hm⟩ := J.2
    let := hm
    let : J.obj.IsKInjective := CochainComplex.isKInjective_of_injective J.obj m
    let eQ := DerivedCategory.quotientCompQhIso C
    obtain ⟨g', hg'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (.up ℤ)).obj I.obj) J.obj).surjective
        (eQ.hom.app I.obj ≫ U.map g ≫ eQ.inv.app J.obj)
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
    have hg : Q.map (ObjectProperty.homMk φ) = g := by
      apply U.map_injective
      change DerivedCategory.Q.map φ = U.map g
      apply (cancel_epi (eQ.hom.app I.obj)).1
      rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg', Category.assoc, Category.assoc]
      erw [eQ.inv_hom_id_app, Category.comp_id]
    have h := F.natural I J hi hj n φ a
    change F.map J hj n ((H n).map (RV.map
      (Q.map (ObjectProperty.homMk φ))) a) =
        F.map I hi n a ≫ (U.map (Q.map (ObjectProperty.homMk φ)))⟦n⟧' at h
    rw [hg] at h
    exact h
  have models (X : DerivedCategory.Plus C) :
      ∃ (I : CochainComplex.Plus C) (hi : ∀ k : ℤ, Injective (I.obj.X k)),
        Nonempty (Q.obj I ≅ X) := by
    obtain ⟨m, hm⟩ := X.2
    let : X.IsGE m := (X.isGE_ι_obj_iff m).1 hm
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X m
    exact ⟨(InjectiveObject.ι C).mapCochainComplexPlus.obj L,
      fun k ↦ (L.obj.X k).2, ⟨e⟩⟩
  choose I hi he using models
  let e (X : DerivedCategory.Plus C) : Q.obj (I X) ≅ X := Classical.choice (he X)
  let post {X Y : DerivedCategory.Plus C} (g : X ⟶ Y) (n : ℤ) :
      (S ⟶ X.obj⟦n⟧) →+ (S ⟶ Y.obj⟦n⟧) :=
    { toFun := fun f ↦ f ≫ (U.map g)⟦n⟧'
      map_zero' := by simp
      map_add' := by intro f g; simp [Preadditive.add_comp] }
  let τ (X : DerivedCategory.Plus C) (n : ℤ) :
      (H n).obj (RV.obj X) →+ (S ⟶ X.obj⟦n⟧) :=
    (post (e X).hom n).comp ((F.map (I X) (hi X) n).comp
      ((H n).map (RV.map (e X).inv)).hom)
  refine ⟨τ, ?_, ?_⟩
  · intro X Y g n a
    let L := RV ⋙ H n
    let g' := (e X).hom ≫ g ≫ (e Y).inv
    have harg : (H n).map (RV.map g') ((H n).map (RV.map (e X).inv) a) =
        (H n).map (RV.map (e Y).inv) ((H n).map (RV.map g) a) := by
      change L.map g' (L.map (e X).inv a) = L.map (e Y).inv (L.map g a)
      rw [← AddCommGrpCat.comp_apply, ← L.map_comp,
        ← AddCommGrpCat.comp_apply, ← L.map_comp]
      congr 2
      simp [g']
    have hn := hnI (I X) (I Y) (hi X) (hi Y) g' n
      ((H n).map (RV.map (e X).inv) a)
    rw [harg] at hn
    change F.map (I Y) (hi Y) n
        ((H n).map (RV.map (e Y).inv) ((H n).map (RV.map g) a)) ≫
          (U.map (e Y).hom)⟦n⟧' =
      (F.map (I X) (hi X) n ((H n).map (RV.map (e X).inv) a) ≫
        (U.map (e X).hom)⟦n⟧') ≫ (U.map g)⟦n⟧'
    rw [hn]
    have hp : (U.map g')⟦n⟧' ≫ (U.map (e Y).hom)⟦n⟧' =
        (U.map (e X).hom)⟦n⟧' ≫ (U.map g)⟦n⟧' := by
      change (U ⋙ shiftFunctor (DerivedCategory C) n).map g' ≫
          (U ⋙ shiftFunctor (DerivedCategory C) n).map (e Y).hom =
        (U ⋙ shiftFunctor (DerivedCategory C) n).map (e X).hom ≫
          (U ⋙ shiftFunctor (DerivedCategory C) n).map g
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp [g']
    simp only [Category.assoc]
    rw [hp]
  · intro J hj n a
    let L := RV ⋙ H n
    have hn := hnI (I (Q.obj J)) J (hi (Q.obj J)) hj (e (Q.obj J)).hom n
      ((H n).map (RV.map (e (Q.obj J)).inv) a)
    have harg : (H n).map (RV.map (e (Q.obj J)).hom)
        ((H n).map (RV.map (e (Q.obj J)).inv) a) = a := by
      change L.map (e (Q.obj J)).hom (L.map (e (Q.obj J)).inv a) = a
      rw [← AddCommGrpCat.comp_apply, ← L.map_comp]
      simp
    rw [harg] at hn
    exact hn.symm

end CategoryTheory.Functor
