/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-! # Pullback of pairings after opposite shifts

Source: the evaluation identification in thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem shift_zero_comp
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (K : C) :
    (F.commShiftIso (0 : ℤ)).hom.app K ≫ (shiftFunctorZero D ℤ).hom.app (F.obj K) =
      F.map ((shiftFunctorZero C ℤ).hom.app K) := by
  simp only [F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, Category.assoc,
    Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

private theorem zero_shift_square
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ]
    (V : C) (W : D) (S : C) (T : D)
    (sy : S ⟶ V⟦(0 : ℤ)⟧) (ds : F.obj S ⟶ T) (a : T ⟶ W⟦(0 : ℤ)⟧)
    (d : F.obj V ⟶ W)
    (h : F.map sy ≫ (F.commShiftIso (0 : ℤ)).hom.app V ≫ d⟦(0 : ℤ)⟧' = ds ≫ a) :
    F.map (sy ≫ (shiftFunctorZero C ℤ).hom.app V) ≫ d =
      ds ≫ a ≫ (shiftFunctorZero D ℤ).hom.app W := by
  have hz := (shiftFunctorZero D ℤ).hom.naturality d
  simp only [Functor.id_map] at hz
  have h' := congrArg (fun x ↦ x ≫ (shiftFunctorZero D ℤ).hom.app W) h
  simp only [Category.assoc] at h'
  rw [hz, ← Category.assoc ((F.commShiftIso (0 : ℤ)).hom.app V), shift_zero_comp] at h'
  simpa only [Functor.map_comp, Category.assoc] using h'

private theorem shifted_comparison
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(upperStar B f).PreservesFlat]
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (upperStar B f).leftDerivedFunctor.map
        ((derivedTensorShiftIso B K M (-2) 2).hom ≫
          (shiftFunctorZero _ ℤ).hom.app _) ≫
        ((leftDerivedUpperStarTensorComparison B f).app K).app M =
      ((leftDerivedUpperStarTensorComparison B f).app (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧) ≫
        derivedTensorHom B
          (((upperStar B f).leftDerivedFunctor.commShiftIso (-2 : ℤ)).hom.app K)
          (((upperStar B f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M) ≫
        (derivedTensorShiftIso B ((upperStar B f).leftDerivedFunctor.obj K)
          ((upperStar B f).leftDerivedFunctor.obj M) (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ := by
  let F := (upperStar B f).leftDerivedFunctor
  have h := zero_shift_square F
    (((derivedTensor B Y).obj K).obj M)
    (((derivedTensor B X).obj (F.obj K)).obj (F.obj M))
    (((derivedTensor B Y).obj (K⟦(-2 : ℤ)⟧)).obj (M⟦(2 : ℤ)⟧))
    (((derivedTensor B X).obj (F.obj (K⟦(-2 : ℤ)⟧))).obj (F.obj (M⟦(2 : ℤ)⟧)))
    (derivedTensorShiftIso B K M (-2) 2).hom
    (((leftDerivedUpperStarTensorComparison B f).app (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧))
    (derivedTensorHom B ((F.commShiftIso (-2 : ℤ)).hom.app K)
      ((F.commShiftIso (2 : ℤ)).hom.app M) ≫
      (derivedTensorShiftIso B (F.obj K) (F.obj M) (-2) 2).hom)
    (((leftDerivedUpperStarTensorComparison B f).app K).app M) (by
      simp only [derivedTensorHom, Category.assoc]
      change (upperStar B f).leftDerivedFunctor.map
          (derivedTensorShiftIso B K M (-2) 2).hom ≫
        (((upperStar B f).leftDerivedFunctor.commShiftIso ((-2 : ℤ) + 2)).hom.app _) ≫
        ((((leftDerivedUpperStarTensorComparison B f).app K).app M)⟦(-2 : ℤ) + 2⟧') =
        ((leftDerivedUpperStarTensorComparison B f).app (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧) ≫
        ((derivedTensor B X).map
          (((upperStar B f).leftDerivedFunctor.commShiftIso (-2 : ℤ)).hom.app K)).app _ ≫
        ((derivedTensor B X).obj _).map
          (((upperStar B f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M) ≫
        (derivedTensorShiftIso B ((upperStar B f).leftDerivedFunctor.obj K)
          ((upperStar B f).leftDerivedFunctor.obj M) (-2) 2).hom
      exact leftDerivedUpperStarTensorComparison_derivedTensorShiftIso B f K M (-2) 2)
  simpa only [Category.assoc] using h

private theorem shifted_pair_map
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}}
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (k : K ⟶ K') (m : M ⟶ M') :
    (derivedTensorShiftIso B K M (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ ≫ derivedTensorHom B k m =
      derivedTensorHom B (k⟦(-2 : ℤ)⟧') (m⟦(2 : ℤ)⟧') ≫
        (derivedTensorShiftIso B K' M' (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ := by
  have hn := (shiftFunctorZero _ ℤ).hom.naturality (derivedTensorHom B k m)
  simp only [Functor.id_map] at hn
  rw [← hn]
  have ht := derivedTensorHom_shift_comp_derivedTensorShiftIso_hom B k m (-2) 2
  change _ = (derivedTensorShiftIso B K M (-2) 2).hom ≫
    (shiftFunctor _ (0 : ℤ)).map (derivedTensorHom B k m) at ht
  rw [← Category.assoc, ← ht, Category.assoc]

private theorem pairing_glue
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {S V U : C} {T W V' W' U' : D}
    (sy : S ⟶ V) (ds : F.obj S ⟶ T) (a : T ⟶ W) (d : F.obj V ⟶ W)
    (p : W ⟶ V') (ps : T ⟶ W') (sx : W' ⟶ V')
    (q : V ⟶ U) (q' : V' ⟶ U') (u : F.obj U ⟶ U')
    (hs : F.map sy ≫ d = ds ≫ a) (hn : a ≫ p = ps ≫ sx)
    (hq : F.map q ≫ u = d ≫ p ≫ q') :
    F.map (sy ≫ q) ≫ u = ds ≫ ps ≫ sx ≫ q' := by
  rw [F.map_comp, Category.assoc, hq, ← Category.assoc (F.map sy) d, hs]
  simp only [Category.assoc]
  rw [← Category.assoc a p, hn]
  simp only [Category.assoc]

private theorem shifted_pairing
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(upperStar B f).PreservesFlat]
    (K M U : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (K' M' U' : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (k : (upperStar B f).leftDerivedFunctor.obj K ⟶ K')
    (m : (upperStar B f).leftDerivedFunctor.obj M ⟶ M')
    (u : (upperStar B f).leftDerivedFunctor.obj U ⟶ U')
    (q : ((derivedTensor B Y).obj K).obj M ⟶ U)
    (q' : ((derivedTensor B X).obj K').obj M' ⟶ U')
    (hq : (upperStar B f).leftDerivedFunctor.map q ≫ u =
      ((leftDerivedUpperStarTensorComparison B f).app K).app M ≫
        derivedTensorHom B k m ≫ q') :
    (upperStar B f).leftDerivedFunctor.map
        ((derivedTensorShiftIso B K M (-2) 2).hom ≫
          (shiftFunctorZero _ ℤ).hom.app _ ≫ q) ≫ u =
      ((leftDerivedUpperStarTensorComparison B f).app (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧) ≫
        derivedTensorHom B
          (((upperStar B f).leftDerivedFunctor.commShiftIso (-2 : ℤ)).hom.app K ≫
            k⟦(-2 : ℤ)⟧')
          (((upperStar B f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M ≫
            m⟦(2 : ℤ)⟧') ≫
        (derivedTensorShiftIso B K' M' (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ ≫ q' := by
  let F := (upperStar B f).leftDerivedFunctor
  let c := derivedTensorHom B ((F.commShiftIso (-2 : ℤ)).hom.app K)
    ((F.commShiftIso (2 : ℤ)).hom.app M)
  have hn := congrArg (fun a ↦ c ≫ a) (shifted_pair_map B k m)
  dsimp only [c] at hn
  simp only [← Category.assoc] at hn
  rw [derivedTensorHom_comp] at hn
  have h := pairing_glue F
    ((derivedTensorShiftIso B K M (-2) 2).hom ≫ (shiftFunctorZero _ ℤ).hom.app _)
    _ _ _ (derivedTensorHom B k m) _
    ((derivedTensorShiftIso B K' M' (-2) 2).hom ≫ (shiftFunctorZero _ ℤ).hom.app _)
    q q' u (shifted_comparison B f K M) (by
      simpa only [Category.assoc] using hn) hq
  simpa only [Category.assoc] using h

/-- Opposite shifts preserve a pairing square for derived inverse image.

Source: the tensor-shift comparison of Stacks Tag 06YU and the shift step in
thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).

Proof: the tensor comparison commutes with the two shifts -2 and 2. Their sum is
zero, and the commutation isomorphism at zero agrees with the canonical shift-zero
isomorphisms. Apply naturality of the tensor-shift isomorphism to the two factor
maps, compose with the given unshifted pairing square, and reassociate. Finally
naturality of the tensor bifunctor puts the positive factor map before the negative
one. No invertibility or nonzero hypothesis on any object is used. -/
theorem derivedPairingOppositeShifts_pullback
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(upperStar B f).PreservesFlat]
    (K M U : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (K' M' U' : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (k : (upperStar B f).leftDerivedFunctor.obj K ⟶ K')
    (m : (upperStar B f).leftDerivedFunctor.obj M ⟶ M')
    (u : (upperStar B f).leftDerivedFunctor.obj U ⟶ U')
    (q : ((derivedTensor B Y).obj K).obj M ⟶ U)
    (q' : ((derivedTensor B X).obj K').obj M' ⟶ U')
    (hq : (upperStar B f).leftDerivedFunctor.map q ≫ u =
      ((leftDerivedUpperStarTensorComparison B f).app K).app M ≫
        ((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).map m ≫
        ((derivedTensor B X).map k).app M' ≫ q') :
    (upperStar B f).leftDerivedFunctor.map
        ((derivedTensorShiftIso B K M (-2) 2).hom ≫
          (shiftFunctorZero _ ℤ).hom.app _ ≫ q) ≫ u =
      ((leftDerivedUpperStarTensorComparison B f).app (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧) ≫
        ((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj
          (K⟦(-2 : ℤ)⟧))).map
          (((upperStar B f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M ≫
            m⟦(2 : ℤ)⟧') ≫
        ((derivedTensor B X).map
          (((upperStar B f).leftDerivedFunctor.commShiftIso (-2 : ℤ)).hom.app K ≫
            k⟦(-2 : ℤ)⟧')).app (M'⟦(2 : ℤ)⟧) ≫
        (derivedTensorShiftIso B K' M' (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ ≫ q' := by
  rw [reassoc_of% (((derivedTensor B X).map k).naturality m)] at hq
  have h := shifted_pairing B f K M U K' M' U' k m u q q'
    (by simpa only [derivedTensorHom, Category.assoc] using hq)
  dsimp only [derivedTensorHom] at h
  simp only [Category.assoc] at h
  rw [← reassoc_of% (((derivedTensor B X).map
    (((upperStar B f).leftDerivedFunctor.commShiftIso (-2 : ℤ)).hom.app K ≫
      k⟦(-2 : ℤ)⟧')).naturality
    (((upperStar B f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M ≫
      m⟦(2 : ℤ)⟧'))] at h
  exact h

end AlgebraicGeometry.Etale
