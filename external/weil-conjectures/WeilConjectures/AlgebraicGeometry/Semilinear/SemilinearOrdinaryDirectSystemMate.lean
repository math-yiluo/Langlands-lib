/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystemCoreData

/-! # Transposition of horizontal compatibility squares

## References

* Zheng Construction 4.1
* Stacks 03D2 and 03DA
* Stacks 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

attribute [local irreducible] evaluation transition

variable (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
  (V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n))
  (a : ∀ n, (I n).modules ⊣ V n)

/-- The local mate assertion for a componentwise direct-image datum.

The assertion is exactly the horizontal compatibility square at two indices,
after transposition by the supplied level adjunctions. -/
def OrdinaryDirectSystemCoreTransitionMate (D : OrdinaryDirectSystemCoreData.{c, v, r}
    (J := J) (B := B) (τ := τ) (J' := J') (F := F) (σ := σ) (V := V)) : Prop :=
  ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m)
    (fm : (evaluation.{c, v, max c v r} J' F σ m).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ m).obj N)
    (fn : (evaluation.{c, v, max c v r} J' F σ n).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ n).obj N),
    let gm := (a m).homEquiv _ _ ((P.component m).inv.app M ≫ fm) ≫
      (D.component m).inv.app N
    let gn := (a n).homEquiv _ _ ((P.component n).inv.app M ≫ fn) ≫
      (D.component n).inv.app N
    (fm ≫ (transition.{c, v, max c v r} J' F σ h).app N =
      (transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)).map fn) ↔
      (gm ≫ (transition.{c, v, max c v r} J B τ h).app (D.push.obj N) =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map gn)

private theorem map_comp_iso_cancel
    {A B : Type*} [Category A] [Category B] (U : A ⥤ B)
    {M N Q : A} (f : M ⟶ N) (q : Q ≅ N) {Z : B} (d : U.obj N ⟶ Z) :
    U.map (f ≫ q.inv) ≫ (U.map q.hom ≫ d) = U.map f ≫ d := by
  simp only [U.map_comp, Category.assoc, ← U.map_comp_assoc, Iso.inv_hom_id,
    U.map_id, Category.id_comp]

private theorem faithful_square_iff
    {A B D : Type*} [Category A] [Category B] [Category D]
    (U : B ⥤ D) [U.Faithful] (X : A ⥤ B)
    {M M' : B} {N N' : A} (f : M ⟶ M') (t : M' ⟶ X.obj N')
    (s : M ⟶ X.obj N) (g : N ⟶ N') :
    (f ≫ t = s ≫ X.map g) ↔
      (U.map f ≫ U.map t = U.map s ≫ (X ⋙ U).map g) := by
  constructor
  · intro h
    simpa only [Functor.map_comp, Functor.comp_map] using congrArg U.map h
  · intro h
    apply U.map_injective
    simpa only [Functor.map_comp, Functor.comp_map] using h

private theorem normalized_square_iff
    {A D : Type*} [Category A] [Category D] {L : A ⥤ D} {R : D ⥤ A}
    (adj : L ⊣ R) {X₁ X₂ P₁ P₂ : A} {Y₁ Y₂ Q₁ Q₂ : D}
    (p₁ : Q₁ ≅ L.obj X₁) (p₂ : Q₂ ≅ L.obj X₂)
    (q₁ : P₁ ≅ R.obj Y₁) (q₂ : P₂ ≅ R.obj Y₂)
    (s : X₁ ⟶ X₂) (t : Y₁ ⟶ Y₂) (s' : Q₁ ⟶ Q₂) (t' : P₁ ⟶ P₂)
    (hs : s' ≫ p₂.hom = p₁.hom ≫ L.map s)
    (ht : t' ≫ q₂.hom = q₁.hom ≫ R.map t)
    (f₁ : Q₁ ⟶ Y₁) (f₂ : Q₂ ⟶ Y₂) (g₁ : X₁ ⟶ P₁) (g₂ : X₂ ⟶ P₂)
    (h₁ : g₁ ≫ q₁.hom = adj.homEquiv _ _ (p₁.inv ≫ f₁))
    (h₂ : g₂ ≫ q₂.hom = adj.homEquiv _ _ (p₂.inv ≫ f₂)) :
    (f₁ ≫ t = s' ≫ f₂) ↔ (g₁ ≫ t' = s ≫ g₂) := by
  have hp : p₁.inv ≫ s' = L.map s ≫ p₂.inv := by
    apply (cancel_mono p₂.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hs, Iso.inv_hom_id_assoc]
  have hleft : (f₁ ≫ t = s' ≫ f₂) ↔
      (L.map s ≫ (p₂.inv ≫ f₂) = (p₁.inv ≫ f₁) ≫ t) := by
    erw [← cancel_epi p₁.inv]
    simp only [← Category.assoc, hp]
    exact eq_comm
  erw [hleft, ← adj.homEquiv_naturality_left_square_iff]
  erw [← h₁, ← h₂]
  erw [← cancel_mono q₂.hom]
  simp only [Category.assoc, ht]
  exact eq_comm

/-- The local mate law for the reassembled componentwise direct image. -/
theorem ordinaryDirectSystem_core_transition_mate_exists [PreservesFiniteLimits uInv]
    (_hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f))
    (D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V))
    (hD : OrdinaryDirectSystemCoreNormalized.{c, v, r} J B τ J' F σ V D uPush eV) :
    OrdinaryDirectSystemCoreTransitionMate.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (I := I) (P := P) (V := V) (a := a) (D := D) := by
  intro M N m n h fm fn
  let p (k : ℕ) :=
    (underlying.{c, v, r} J' (F k)).mapIso ((P.component k).app M) ≪≫
      (I k).moduleUnderlying.app ((evaluation.{c, v, max c v r} J B τ k).obj M)
  let q (k : ℕ) :=
    (underlying.{c, v, r} J (B k)).mapIso ((D.component k).app N) ≪≫
      (eV k).app ((evaluation.{c, v, max c v r} J' F σ k).obj N)
  have hs :
      (underlying.{c, v, r} J' (F m)).map
          ((transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M)) ≫ (p n).hom =
        (p m).hom ≫ uInv.map ((underlying.{c, v, r} J (B m)).map
          ((transition.{c, v, max c v r} J B τ h).app M)) := by
    have ht := congrArg ((underlying.{c, v, r} J' (F m)).map) (P.transition h M)
    simp only [Functor.map_comp] at ht
    dsimp only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    calc
      _ = ((underlying.{c, v, r} J' (F m)).map
            ((transition J' F σ h).app (P.pull.obj M)) ≫
          (underlying.{c, v, r} J' (F n)).map ((P.component n).hom.app M)) ≫
            (I n).moduleUnderlying.hom.app ((evaluation J B τ n).obj M) :=
        (Category.assoc _ _ _).symm
      _ = ((underlying.{c, v, r} J' (F m)).map ((P.component m).hom.app M) ≫
          (underlying.{c, v, r} J' (F m)).map
            ((I m).modules.map ((transition J B τ h).app M)) ≫
          (underlying.{c, v, r} J' (F m)).map
            ((P.restriction h).hom.app ((evaluation J B τ n).obj M))) ≫
            (I n).moduleUnderlying.hom.app ((evaluation J B τ n).obj M) :=
        congrArg (· ≫ (I n).moduleUnderlying.hom.app
          ((evaluation J B τ n).obj M)) ht
      _ = (underlying.{c, v, r} J' (F m)).map ((P.component m).hom.app M) ≫
          (underlying.{c, v, r} J' (F m)).map
            ((I m).modules.map ((transition J B τ h).app M)) ≫
          ((underlying.{c, v, r} J' (F m)).map
            ((P.restriction h).hom.app ((evaluation J B τ n).obj M)) ≫
            (I n).moduleUnderlying.hom.app ((evaluation J B τ n).obj M)) := by
        simp only [Category.assoc]
      _ = (underlying.{c, v, r} J' (F m)).map ((P.component m).hom.app M) ≫
          (underlying.{c, v, r} J' (F m)).map
            ((I m).modules.map ((transition J B τ h).app M)) ≫
          (I m).moduleUnderlying.hom.app
            ((res (coefficientMap J B τ h)).obj ((evaluation J B τ n).obj M)) :=
        congrArg ((underlying.{c, v, r} J' (F m)).map ((P.component m).hom.app M) ≫
          (underlying.{c, v, r} J' (F m)).map
            ((I m).modules.map ((transition J B τ h).app M)) ≫ ·)
          (P.restriction_underlying h ((evaluation J B τ n).obj M))
      _ = _ :=
        (congrArg ((underlying.{c, v, r} J' (F m)).map
          ((P.component m).hom.app M) ≫ ·)
          ((I m).moduleUnderlying.hom.naturality ((transition J B τ h).app M))).trans
            (Category.assoc _ _ _).symm
  have ht :
      (underlying.{c, v, r} J (B m)).map
          ((transition.{c, v, max c v r} J B τ h).app (D.push.obj N)) ≫ (q n).hom =
        (q m).hom ≫ uPush.map ((underlying.{c, v, r} J' (F m)).map
          ((transition.{c, v, max c v r} J' F σ h).app N)) := by
    exact (hD N h).trans (Category.assoc _ _ _).symm
  have hg (k : ℕ)
      (f : (evaluation.{c, v, max c v r} J' F σ k).obj (P.pull.obj M) ⟶
        (evaluation.{c, v, max c v r} J' F σ k).obj N) :
      (underlying.{c, v, r} J (B k)).map
        ((a k).homEquiv _ _ ((P.component k).inv.app M ≫ f) ≫
          (D.component k).inv.app N) ≫ (q k).hom =
        adjSet.homEquiv _ _ ((p k).inv ≫
          (underlying.{c, v, r} J' (F k)).map f) := by
    dsimp only [q, p, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
    calc
      _ = (underlying.{c, v, r} J (B k)).map
            ((a k).homEquiv _ _ ((P.component k).inv.app M ≫ f)) ≫
          (eV k).hom.app ((evaluation J' F σ k).obj N) :=
        map_comp_iso_cancel (underlying.{c, v, r} J (B k))
          ((a k).homEquiv _ _ ((P.component k).inv.app M ≫ f))
          ((D.component k).app N) _
      _ = adjSet.homEquiv _ _ ((I k).moduleUnderlying.inv.app
          ((evaluation J B τ k).obj M) ≫
            (underlying.{c, v, r} J' (F k)).map ((P.component k).inv.app M ≫ f)) :=
        ha k _ _ _
      _ = _ := congrArg (adjSet.homEquiv _ _) (by
        simp only [Functor.map_comp, Category.assoc])
  let gm := (a m).homEquiv _ _ ((P.component m).inv.app M ≫ fm) ≫
    (D.component m).inv.app N
  let gn := (a n).homEquiv _ _ ((P.component n).inv.app M ≫ fn) ≫
    (D.component n).inv.app N
  have he := normalized_square_iff adjSet (p m) (p n) (q m) (q n)
    ((underlying.{c, v, r} J (B m)).map
      ((transition.{c, v, max c v r} J B τ h).app M))
    ((underlying.{c, v, r} J' (F m)).map
      ((transition.{c, v, max c v r} J' F σ h).app N))
    ((underlying.{c, v, r} J' (F m)).map
      ((transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M)))
    ((underlying.{c, v, r} J (B m)).map
      ((transition.{c, v, max c v r} J B τ h).app (D.push.obj N))) hs ht
    ((underlying.{c, v, r} J' (F m)).map fm)
    ((underlying.{c, v, r} J' (F n)).map fn)
    ((underlying.{c, v, r} J (B m)).map gm)
    ((underlying.{c, v, r} J (B n)).map gn) (hg m fm) (hg n fn)
  have hl := faithful_square_iff (underlying.{c, v, r} J' (F m))
    (res (coefficientMap J' F σ h)) fm
    ((transition J' F σ h).app N) ((transition J' F σ h).app (P.pull.obj M)) fn
  have hr := faithful_square_iff (underlying.{c, v, r} J (B m))
    (res (coefficientMap J B τ h)) gm
    ((transition J B τ h).app (D.push.obj N)) ((transition J B τ h).app M) gn
  exact hl.trans (he.trans hr.symm)

end WeilConjectures.SemilinearSections
end
