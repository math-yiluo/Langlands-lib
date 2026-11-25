/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility

/-! # Pullback of flat single-object pairings after symmetry

Source: Stacks Tags 06YQ and 06YU
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem swap_naturality
    {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) (s : T ≅ T.flip)
    {L L' M M' : C} (l : L ⟶ L') (m : M ⟶ M') :
    (T.obj L).map m ≫ (T.map l).app M' ≫ (s.hom.app L').app M' =
      (s.hom.app L).app M ≫ (T.map m).app L ≫ (T.obj M').map l := by
  have h := congr_app (s.hom.naturality l) M'
  change (T.map l).app M' ≫ (s.hom.app L').app M' =
    (s.hom.app L).app M' ≫ (T.obj M').map l at h
  rw [h]
  rw [← Category.assoc, (s.hom.app L).naturality m]
  simp only [Functor.flip_obj_map, Category.assoc]

private theorem swap_pairing_pullback
    {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D) (F : C ⥤ D)
    (s : T ≅ T.flip) (s' : T' ≅ T'.flip)
    (L M U : C) (L' M' U' : D)
    (l : F.obj L ⟶ L') (m : F.obj M ⟶ M') (u : F.obj U ⟶ U')
    (q : (T.obj M).obj L ⟶ U) (q' : (T'.obj M').obj L' ⟶ U')
    (d : F.obj ((T.obj L).obj M) ⟶ (T'.obj (F.obj L)).obj (F.obj M))
    (d' : F.obj ((T.obj M).obj L) ⟶ (T'.obj (F.obj M)).obj (F.obj L))
    (hs : F.map ((s.hom.app L).app M) ≫ d' =
      d ≫ (s'.hom.app (F.obj L)).app (F.obj M))
    (hq : F.map q ≫ u = d' ≫ (T'.map m).app _ ≫ (T'.obj M').map l ≫ q') :
    F.map ((s.hom.app L).app M ≫ q) ≫ u =
      d ≫ (T'.obj (F.obj L)).map m ≫ (T'.map l).app M' ≫
        (s'.hom.app L').app M' ≫ q' := by
  simp only [F.map_comp, Category.assoc]
  rw [hq, ← Category.assoc (F.map _) d', hs]
  simp only [Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun a ↦ d ≫ a ≫ q') (swap_naturality T' s' l m).symm

/-- A flat degree-zero pairing remains compatible with pullback after swapping its factors.

Source: Stacks Tags 06YQ and 06YU; the symmetry step of the finite-line evaluation argument
(auxiliary; not a blueprint node).

Proof: lift the given ordinary pairing square using the pullback field of
etaleSingleFunctor_monoidalCompatibility. Use the supplied braiding square for the
derived inverse-image tensor comparison. Compose that braiding square with the
lifted pairing square,
then use naturality of the derived symmetry to move both factor comparisons across it.
This gives the negative-first pairing square in the displayed order. Only the left
factors L and L' need to be flat; the other factors and the pairings are arbitrary. -/
theorem flatSinglePairing_symmetricPullback
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hsym : ∀ K M : DerivedCategory (Sheaf Y.smallEtaleTopology B),
      (upperStar B f).leftDerivedFunctor.map
        (((derivedTensorSymmetry B Y).hom.app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison B f).app M).app K =
      ((leftDerivedUpperStarTensorComparison B f).app K).app M ≫
        ((derivedTensorSymmetry B X).hom.app
          ((upperStar B f).leftDerivedFunctor.obj K)).app
          ((upperStar B f).leftDerivedFunctor.obj M))
    (L M P : Sheaf Y.smallEtaleTopology B)
    (L' M' P' : Sheaf X.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
    (q : L ⊗ M ⟶ P) (q' : L' ⊗ M' ⟶ P')
    (l : (upperStar B f).obj L ⟶ L')
    (m : (upperStar B f).obj M ⟶ M')
    (p : (upperStar B f).obj P ⟶ P')
    (w : (upperStar B f).map q ≫ p =
      Functor.OplaxMonoidal.δ (upperStar B f) L M ≫
        (l ⊗ₘ m) ≫ q') :
    (upperStar B f).leftDerivedFunctor.map
      (((derivedTensorSymmetry B Y).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M)).app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
        singleFunctorFlatPairing L M P hL q) ≫ singleFunctorPullbackMap f p =
      ((leftDerivedUpperStarTensorComparison B f).app
        ((DerivedCategory.singleFunctor _ 0).obj M)).app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
      ((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))).map (singleFunctorPullbackMap f l) ≫
      ((derivedTensor B X).map (singleFunctorPullbackMap f m)).app _ ≫
      ((derivedTensorSymmetry B X).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M')).app
        ((DerivedCategory.singleFunctor _ 0).obj L') ≫
        singleFunctorFlatPairing L' M' P' hL' q' := by
  have hp := (etaleSingleFunctor_monoidalCompatibility B f).pullback
    hL hL' q q' l m p w
  exact swap_pairing_pullback
    (derivedTensor B Y) (derivedTensor B X) (upperStar B f).leftDerivedFunctor
    (derivedTensorSymmetry B Y)
    (derivedTensorSymmetry B X)
    _ _ _ _ _ _ (singleFunctorPullbackMap f m) (singleFunctorPullbackMap f l)
    (singleFunctorPullbackMap f p) _ _ _ _
    (hsym _ _) hp

end AlgebraicGeometry.Etale
