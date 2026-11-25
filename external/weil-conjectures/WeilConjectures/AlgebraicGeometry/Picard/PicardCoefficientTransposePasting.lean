/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorSinglePullbackComposition
import WeilConjectures.AlgebraicGeometry.DerivedSquareVerticalPasting

/-! # Pasting of the coefficient transpose

## References

* Stacks Project, Tags 08HY and 0D5S
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The counit presentation of a coefficient transpose for an arbitrary square. -/
@[irreducible]
def coefficientCounitTranspose {A B W V : Scheme.{v}}
    (p : A ⟶ W) (p' : B ⟶ V) (r : V ⟶ W) (a : B ⟶ A)
    (ha : a ≫ p = p' ≫ r) (K : schemeDerivedCategory A)
    (N : schemeDerivedCategory B) (e : (derivedPullback a).obj K ⟶ N) :
    (derivedPullback p').obj
      ((derivedPullback r).obj ((schemeDerivedDirectImage p).obj K)) ⟶ N :=
  canonicalDerivedSquareComparison p p' r a ha ((schemeDerivedDirectImage p).obj K) ≫
    (derivedPullback a).map ((canonicalSchemeDerivedAdjunction p).counit.app K) ≫ e

/-- Defining equation for the counit coefficient transpose. -/
theorem coefficientCounitTranspose_eq {A B W V : Scheme.{v}}
    (p : A ⟶ W) (p' : B ⟶ V) (r : V ⟶ W) (a : B ⟶ A)
    (ha : a ≫ p = p' ≫ r) (K : schemeDerivedCategory A)
    (N : schemeDerivedCategory B) (e : (derivedPullback a).obj K ⟶ N) :
    coefficientCounitTranspose p p' r a ha K N e =
      canonicalDerivedSquareComparison p p' r a ha ((schemeDerivedDirectImage p).obj K) ≫
        (derivedPullback a).map ((canonicalSchemeDerivedAdjunction p).counit.app K) ≫ e := by
  delta coefficientCounitTranspose
  rfl

/-- The coefficient transpose, constructed from the fixed base-change mate. -/
@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
    exact coefficientCounitTranspose (pullback.snd f k)
      (pullback.snd f (r ≫ k)) r a hb K _
      (tensorSingleCoefficientMap (pullback.fst f k)
        (pullback.fst f (r ≫ k)) a ha L)

omit [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))] in
private theorem paste_coherent_comparisons
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (A : F ⋙ G ⟶ H)
    {P K : C} {Q Z1 : D} {Q' Z0 Z2 : E}
    (ε : P ⟶ K) (e : F.obj K ⟶ Q) (ej : G.obj Q ⟶ Q')
    (e' : H.obj K ⟶ Q') (Dj : Z0 ⟶ G.obj Z1) (d : Z1 ⟶ F.obj P)
    (d' : Z2 ⟶ H.obj P) (c : Z0 ⟶ Z2)
    (hs : Dj ≫ G.map d ≫ A.app P = c ≫ d')
    (he : G.map e ≫ ej = A.app K ≫ e') :
    Dj ≫ G.map (d ≫ F.map ε ≫ e) ≫ ej = c ≫ d' ≫ H.map ε ≫ e' := by
  have hn := A.naturality ε
  change G.map (F.map ε) ≫ A.app K = A.app P ≫ H.map ε at hn
  calc
    _ = Dj ≫ G.map d ≫ G.map (F.map ε) ≫ A.app K ≫ e' := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun z ↦ Dj ≫ G.map d ≫ G.map (F.map ε) ≫ z) he
    _ = Dj ≫ G.map d ≫ A.app P ≫ H.map ε ≫ e' := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ Dj ≫ G.map d ≫ z ≫ e') hn
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ H.map ε ≫ e') hs

omit [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))] in
private theorem paste_evaluated_comparisons
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (A : F ⋙ G ⟶ H)
    {P K : C} {Q Z1 : D} {Q' Z0 Z2 : E}
    (ε : P ⟶ K) (e : F.obj K ⟶ Q) (ej : G.obj Q ⟶ Q')
    (e' : H.obj K ⟶ Q') (Dj : Z0 ⟶ G.obj Z1) (d : Z1 ⟶ F.obj P)
    (d' : Z2 ⟶ H.obj P) (c : Z0 ⟶ Z2)
    (z : Z1 ⟶ Q) (z' : Z2 ⟶ Q')
    (hz : z = d ≫ F.map ε ≫ e) (hz' : z' = d' ≫ H.map ε ≫ e')
    (hs : Dj ≫ G.map d ≫ A.app P = c ≫ d')
    (he : G.map e ≫ ej = A.app K ≫ e') :
    Dj ≫ G.map z ≫ ej = c ≫ z' := by
  rw [hz, hz']
  exact paste_coherent_comparisons F G H A ε e ej e' Dj d d' c hs he

/-- Pasting API for the counit construction on arbitrary scheme squares. -/
private theorem coefficientCounitTranspose_pasting
    {A B C X W T T' : Scheme.{v}}
    (p : A ⟶ W) (p1 : B ⟶ T) (p2 : C ⟶ T')
    (t : T ⟶ W) (i : T' ⟶ T) (t' : T' ⟶ W)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (ha : a ≫ p = p1 ≫ t) (hb : b ≫ p1 = p2 ≫ i)
    (ha' : a' ≫ p = p2 ≫ t') (h : i ≫ t = t') (hab : b ≫ a = a')
    (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (L : X.Modules) :
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
        ((Modules.tensorPullback q).obj L)
    let E := (schemeDerivedDirectImage p).obj K
    let e := tensorSingleCoefficientMap q q1 a h1 L
    let e' := tensorSingleCoefficientMap q q2 a' h3 L
    canonicalDerivedSquareComparison p1 p2 i b hb ((derivedPullback t).obj E) ≫
      (derivedPullback b).map (coefficientCounitTranspose p p1 t a ha K _ e) ≫
      tensorSingleCoefficientMap q1 q2 b h2 L =
    (derivedPullback p2).map
      ((canonicalDerivedPullbackComposition i t ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback r) h)).hom.app E) ≫
      coefficientCounitTranspose p p2 t' a' ha' K _ e' := by
  classical
  intro K E e e'
  let ε := (canonicalSchemeDerivedAdjunction p).counit.app K
  let D := canonicalDerivedSquareComparison p p1 t a ha E
  let D' := canonicalDerivedSquareComparison p p2 t' a' ha' E
  let Dj := canonicalDerivedSquareComparison p1 p2 i b hb ((derivedPullback t).obj E)
  let c := (derivedPullback p2).map
    ((canonicalDerivedPullbackComposition i t ≪≫
      eqToIso (congrArg (fun r ↦ derivedPullback r) h)).hom.app E)
  let comp := canonicalDerivedPullbackComposition b a ≪≫
    eqToIso (congrArg (fun r ↦ derivedPullback r) hab)
  have hs := canonicalDerivedSquareComparison_vertical p p1 p2 t i t' a b a'
    ha hb ha' h hab E
  have he := tensorSingleCoefficientMap_composition q q1 q2 a b a' h1 h2 h3 hab L
  exact paste_evaluated_comparisons (derivedPullback a) (derivedPullback b)
    (derivedPullback a') comp.hom ε e (tensorSingleCoefficientMap q1 q2 b h2 L)
    e' Dj D D' c (coefficientCounitTranspose p p1 t a ha K _ e)
    (coefficientCounitTranspose p p2 t' a' ha' K _ e')
    (coefficientCounitTranspose_eq p p1 t a ha K _ e)
    (coefficientCounitTranspose_eq p p2 t' a' ha' K _ e') hs he

set_option cleanup.letToHave false in
-- The selected adjunction and coefficient isomorphisms have large dependent types.
/-- Coefficient pasting for the transposes of base change, with no structure-sheaf
normalization and no test section. -/
theorem picardCoefficientTranspose_pasting
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (h : i ≫ t = t')
    (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k))
    (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k))
    (hj₂ : j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i)
 :
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
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  let C := canonicalDerivedPullbackComposition i t ≪≫
    eqToIso (congrArg (fun q : T' ⟶ W ↦ derivedPullback q) h)
  let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
  let c := (conjugateIsoEquiv
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t ≫ k)))).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
    (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f (t' ≫ k))))).symm
    (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
      Modules.pushforwardCongr hj₁)
  let d := ((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction j)).symm.app N ≪≫ (c.app L).symm
  canonicalDerivedSquareComparison (pullback.snd f (t ≫ k))
      (pullback.snd f (t' ≫ k)) i j hj₂ ((derivedPullback t).obj E) ≫
    (derivedPullback j).map (τ t) ≫ Modules.canonicalSinglePullbackMap j N ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (t' ≫ k)).toRingedSpace)) 0).map
          d.hom =
    (derivedPullback (pullback.snd f (t' ≫ k))).map (C.hom.app E) ≫ τ t' := by
  classical
  intro τ E C N cj dj
  have hdj : dj = Modules.tensorCoefficientComparison (pullback.fst f (t ≫ k))
      (pullback.fst f (t' ≫ k)) j hj₁ L :=
    (Modules.tensorCoefficientComparison_eq (pullback.fst f (t ≫ k))
      (pullback.fst f (t' ≫ k)) j hj₁ L).symm
  rw [hdj, ← tensorSingleCoefficientMap_eq]
  clear hdj dj cj
  let a : pullback f (t ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t ≫ k)) (pullback.snd f (t ≫ k) ≫ t)
      (by rw [Category.assoc]; exact pullback.condition)
  let a' : pullback f (t' ≫ k) ⟶ pullback f k :=
    pullback.lift (pullback.fst f (t' ≫ k)) (pullback.snd f (t' ≫ k) ≫ t')
      (by rw [Category.assoc]; exact pullback.condition)
  have ha₁ : a ≫ pullback.fst f k = pullback.fst f (t ≫ k) := pullback.lift_fst ..
  have ha₂ : a ≫ pullback.snd f k = pullback.snd f (t ≫ k) ≫ t := pullback.lift_snd ..
  have ha'₁ : a' ≫ pullback.fst f k = pullback.fst f (t' ≫ k) := pullback.lift_fst ..
  have ha'₂ : a' ≫ pullback.snd f k = pullback.snd f (t' ≫ k) ≫ t' :=
    pullback.lift_snd ..
  have hja : j ≫ a = a' := by
    apply pullback.hom_ext
    · rw [Category.assoc, ha₁, hj₁, ha'₁]
    · rw [Category.assoc, ha₂, ← Category.assoc, hj₂, Category.assoc, h, ha'₂]
  dsimp only [τ]
  delta picardCoefficientTranspose
  exact coefficientCounitTranspose_pasting (pullback.snd f k)
    (pullback.snd f (t ≫ k)) (pullback.snd f (t' ≫ k)) t i t' a j a'
    ha₂ hj₂ ha'₂ h hja (pullback.fst f k) (pullback.fst f (t ≫ k))
    (pullback.fst f (t' ≫ k)) ha₁ hj₁ ha'₁ L

end
end AlgebraicGeometry.Scheme
