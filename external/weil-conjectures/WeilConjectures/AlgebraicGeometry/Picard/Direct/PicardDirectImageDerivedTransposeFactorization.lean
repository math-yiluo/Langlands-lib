/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageDerivedTranspose
public import WeilConjectures.AlgebraicGeometry.Picard.PicardCoefficientTransposePasting
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedUnitNormalizationComposition

/-! # Factorization of the normalized transpose

## References

* Stacks Project, Tag 08HY
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section
private theorem transpose_three_maps
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B E : C} {N : D} (a : B ⟶ A) (ζ : A ⟶ E) (b : E ⟶ G.obj N) :
    (adj.homEquiv B N).symm (a ≫ ζ ≫ b) =
      F.map (a ≫ ζ) ≫ (adj.homEquiv E N).symm b := by
  rw [← Category.assoc a ζ, adj.homEquiv_naturality_left_symm]

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/- The coefficient mate evaluation is needed only because the definition is now
written in its equal counit presentation. -/
private theorem coefficientMate_evaluation
    {A B W V : Scheme.{v}} (p : A ⟶ W) (p' : B ⟶ V)
    (r : V ⟶ W) (a : B ⟶ A) (ha : a ≫ p = p' ≫ r)
    (K : schemeDerivedCategory A) (N : schemeDerivedCategory B)
    (e : (derivedPullback a).obj K ⟶ N) :
    ((canonicalSchemeDerivedAdjunction p').homEquiv _ _).symm
      (schemeDerivedBaseChangeMap p p' r a ha K ≫
        (schemeDerivedDirectImage p').map e) =
    canonicalDerivedSquareComparison p p' r a ha ((schemeDerivedDirectImage p).obj K) ≫
      (derivedPullback a).map ((canonicalSchemeDerivedAdjunction p).counit.app K) ≫ e := by
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    schemeDerivedMate_evaluation, Category.assoc]

/-- Evaluate the coefficient mate before specializing its square to a fibre product. -/
private theorem coefficientMate_tensor_evaluation
    {A B X W V : Scheme.{v}} (p : A ⟶ W) (p' : B ⟶ V)
    (r : V ⟶ W) (a : B ⟶ A) (ha : a ≫ p = p' ≫ r)
    (q : A ⟶ X) (q' : B ⟶ X) (hq : a ≫ q = q') (L : X.Modules) :
    let M := (Modules.tensorPullback q).obj L
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj M
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction q)).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction a)))
      (Classical.choose (Modules.exists_tensorPullbackAdjunction q'))).symm
      (Modules.pushforwardComp a q ≪≫ Modules.pushforwardCongr hq)
    let d := ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction a)).symm.app M ≪≫ (c.app L).symm
    ((canonicalSchemeDerivedAdjunction p').homEquiv _ _).symm
      (schemeDerivedBaseChangeMap p p' r a ha K ≫
        (schemeDerivedDirectImage p').map
          (Modules.canonicalSinglePullbackMap a M ≫
            (DerivedCategory.singleFunctor _ 0).map d.hom)) =
      coefficientCounitTranspose p p' r a ha K _ (tensorSingleCoefficientMap q q' a hq L) := by
  intro M K c d
  rw [coefficientCounitTranspose_eq, tensorSingleCoefficientMap_eq,
    Modules.tensorCoefficientComparison_eq]
  exact coefficientMate_evaluation p p' r a ha K _ _

-- Keep the explicitly constructed coefficient comparison folded.
/-- The normalized transpose factors through the coefficient transpose. -/
theorem picardDirectImageDerivedTranspose_factorization
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {V : Scheme.{v}} (r : V ⟶ W)
    (ζ : picardDerivedModelSections
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) r) :
  let τ : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
    picardCoefficientTranspose f L W k
  let e : ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings V.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings V.toRingedSpace)) :=
    picardDerivedUnitNormalization W
  picardDirectImageDerivedTranspose f L W k r ζ =
    (derivedPullback (pullback.snd f (r ≫ k))).map ((e r).inv ≫ ζ) ≫ τ r := by
  classical
  intro τ e
  unfold picardDirectImageDerivedTranspose
  dsimp only [τ, e]
  unfold picardCoefficientTranspose picardDerivedUnitNormalization
  refine (transpose_three_maps _ _ _ _).trans ?_
  congr 1
  exact coefficientMate_tensor_evaluation _ _ _ _ _ _ _ _ _

end
end AlgebraicGeometry.Scheme
