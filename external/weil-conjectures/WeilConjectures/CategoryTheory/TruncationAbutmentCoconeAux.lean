/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

@[expose] public section
universe u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory


/-- Auxiliary compatibility package for the normalized truncation cocone.
Source: Stacks Tag 05TC (2), blueprint step 5; (blueprint: lem-sp-truncation-abutment-cocone-aux)
Proof: Normalize the total-degree and truncation indices of alpha, cancel the two bridge
isomorphisms, combine the three functor maps, and use transition_comp_ιTruncLE and
transport naturality for the inclusion. For c, the inclusion tau_{<=n}K -> K is a
cohomology isomorphism through n and has zero source cohomology in degree n+1. Apply the
proved low-degree right-derived map theorem on D+ and transport it by the natural
bounded-below/unbounded derived-functor comparison. Composing with the inverse bridge
and the object transports proves c invertible. Finally normalize j to a diagonal family
k; induct on the alpha iterate, using the cocone identity at each successor and hc at
the endpoint. This also covers page zero, where the iterate is the identity. -/
theorem truncation_abutment_cocone_aux
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (X : BigradedExactCouple B 0)
    (hD : X.D = TruncationCouple.D F K)
    (halpha : ∀ p q : ℤ, X.alpha p q =
      eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
        eqToHom (by rw [hD]))
    (H : ℤ → B) (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
    (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
    (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
    (hj : ∀ n q, j n q = eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
      (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
      eqToHom (by rw [hH]))
    (hc : ∀ n, c n = eqToHom (by congr 1; omega) ≫ j n n) :
    (∀ n, IsIso (c n)) ∧
    (∀ n p, X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n-p) =
      eqToHom (by congr 1; omega) ≫ j n (n-(p+1))) ∧
    (∀ (n p : ℤ) (_ : 0 ≤ p), eqToHom (by congr 1 <;> omega) ≫ j n (n-p) =
      X.incomingAlphaIter p.toNat 0 n ≫ c n) := by
  have hco :
    (∀ n p, X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n-p) =
      eqToHom (by congr 1; omega) ≫ j n (n-(p+1))) := by
    have ha (p q n t : ℤ) (hn : p + q = n) (ht : q + 1 = t) :
        TruncationCouple.alpha F K p q =
          eqToHom (by unfold TruncationCouple.D; rw [hn]) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map
              (eqToHom (congrArg (fun r : ℤ ↦ K.obj.truncLE r)
                (by omega : q = t - 1)) ≫ TruncationCouple.transition K t))) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K t) n).hom ≫
          eqToHom (by unfold TruncationCouple.D; rw [← ht, ← hn]; congr 1; omega) := by
      subst n
      subst t
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    cases X
    dsimp only at hD
    subst hD
    subst hH
    dsimp only at halpha hj hc
    intro n p
    simp only [BigradedExactCouple.alphaDiagonal, halpha]
    rw [ha (p + 1) (n - (p + 1)) n (n - p) (by omega) (by omega)]
    simp only [hj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    have hq : n - (p + 1) = n - p - 1 := by omega
    simp only [Category.assoc, TruncationCouple.transition_comp_ιTruncLE]
    have hι := eqToHom_naturality (fun r : ℤ ↦ K.obj.ιTruncLE r) hq
    simp only [eqToHom_refl, Category.comp_id] at hι
    rw [hι]
  refine ⟨?_, hco, ?_⟩
  · intro n
    let L : DerivedCategory.Plus A := ⟨DerivedCategory.Q.obj (K.obj.truncLE n), by
      obtain ⟨a, ha⟩ := (TruncationCouple.truncation K n).property
      change (K.obj.truncLE n).IsStrictlyGE a at ha
      have := ha
      exact ⟨a, inferInstance⟩⟩
    let M : DerivedCategory.Plus A := ⟨DerivedCategory.Q.obj K.obj, by
      obtain ⟨a, ha⟩ := K.property
      have := ha
      exact ⟨a, inferInstance⟩⟩
    let f : L ⟶ M := ObjectProperty.homMk (DerivedCategory.Q.map (K.obj.ιTruncLE n))
    have hlow (i : ℤ) (hi : i ≤ n) :
        IsIso ((DerivedCategory.Plus.homologyFunctor A i).map f) := by
      change IsIso ((DerivedCategory.homologyFunctor A i).map
        (DerivedCategory.Q.map (K.obj.ιTruncLE n)))
      have : QuasiIsoAt (K.obj.ιTruncLE n) i :=
        K.obj.quasiIsoAt_ιTruncLE n i hi
      have he := DerivedCategory.homologyFunctorFactors_hom_naturality (K.obj.ιTruncLE n) i
      have : IsIso (HomologicalComplex.homologyMap (K.obj.ιTruncLE n) i) := inferInstance
      have : IsIso ((DerivedCategory.homologyFunctor A i).map
          (DerivedCategory.Q.map (K.obj.ιTruncLE n)) ≫
          (DerivedCategory.homologyFunctorFactors A i).hom.app K.obj) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((DerivedCategory.homologyFunctorFactors A i).hom.app K.obj)
    have hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map f) := by
      have hz : IsZero ((DerivedCategory.Plus.homologyFunctor A (n + 1)).obj L) := by
        change IsZero ((DerivedCategory.homologyFunctor A (n + 1)).obj
          (DerivedCategory.Q.obj (K.obj.truncLE n)))
        exact (DerivedCategory.Q.obj (K.obj.truncLE n)).isZero_of_isLE n (n + 1) (by omega)
      exact hz.mono _
    have hplus := F.isIso_homologyFunctor_rightDerivedFunctorPlus_map n f hlow hmono n (by omega)
    have : IsIso ((DerivedCategory.homologyFunctor B n).map
        ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map f)) := hplus
    have he := (F.rightDerivedFunctorPlusCompatibility.inv.naturality f)
    have hmap := (DerivedCategory.homologyFunctor B n).congr_map he
    have hraw : IsIso ((DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) := by
      have : IsIso ((DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor).map f)) := by
        have : IsIso ((DerivedCategory.homologyFunctor B n).map
            ((DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor).map f) ≫
            (DerivedCategory.homologyFunctor B n).map
              (F.rightDerivedFunctorPlusCompatibility.inv.app M)) := by
          simp only [Functor.map_comp] at hmap
          rw [hmap]
          infer_instance
        exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctorPlusCompatibility.inv.app M))
      exact this
    rw [hc, hj]
    infer_instance
  · let k (n p : ℤ) : X.D p (n - p) ⟶ H n :=
      eqToHom (by congr 1; omega) ≫ j n (n - p)
    have hk (n p : ℤ) : X.alphaDiagonal n p ≫ k n p = k n (p + 1) := hco n p
    have hi (n : ℤ) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
        X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ k n (p - r) =
          eqToHom (by congr 1; omega) ≫ k n p := by
      induction r generalizing p q with
      | zero =>
        simp only [BigradedExactCouple.alphaIter, eqToHom_trans_assoc]
        have he := eqToHom_naturality (k n) (by omega : p - (↑(0 : ℕ) : ℤ) = p)
        simp only [eqToHom_refl, Category.comp_id] at he
        rw [he, eqToHom_trans_assoc]
      | succ r ih =>
        simp only [BigradedExactCouple.alphaIter, Category.assoc, eqToHom_trans_assoc]
        have he := ih (p - 1) (q + 1) (by omega)
        have hidx : p - ↑(r + 1 : ℕ) = p - 1 - ↑r := by omega
        have hcast := eqToHom_naturality (k n) hidx
        simp only [eqToHom_refl, Category.comp_id] at hcast
        rw [hcast, eqToHom_trans_assoc]
        rw [he]
        have hq : q = n - p := by omega
        subst q
        have he' := hk n (p - 1)
        simp only [BigradedExactCouple.alphaDiagonal, Category.assoc] at he'
        dsimp only [k] at he' ⊢
        simp only [eqToHom_trans_assoc] at he' ⊢
        convert! he' using 1 <;> congr! 4 <;> omega
    intro n p hp
    lift p to ℕ using hp
    have he := hi n p (p : ℤ) (n - p) (by omega)
    have hend := eqToHom_naturality (k n) (by omega : (p : ℤ) - p = 0)
    simp only [eqToHom_refl, Category.comp_id] at hend
    rw [hend, eqToHom_trans_assoc] at he
    simp only [k, eqToHom_trans_assoc] at he
    simp only [Int.toNat_natCast, BigradedExactCouple.incomingAlphaIter, hc,
      Category.assoc, eqToHom_trans_assoc]
    convert! he.symm using 1 <;> congr! 4 <;> omega

end CategoryTheory
