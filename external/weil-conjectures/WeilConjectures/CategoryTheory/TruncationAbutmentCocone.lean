/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.TruncationAbutmentCoconeAux

/-! Canonical maps from a truncation diagonal to derived cohomology. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Canonical truncation maps form a normalized diagonal cocone whose degree-zero
component is invertible.
Source: Stacks Tag 05TC (2), and truncation spectral sequence blueprint step 5.
(blueprint: lem-sp-truncation-abutment-cocone)

Proof: Set H to the cohomology of RF(K), j to the inverse bridge followed by
RF of the truncation inclusion, and c to the degree-zero component of j.
The inclusion tau<=n K -> K induces an isomorphism in degree n by 05TC (2);
transport this isomorphism through the bridge to obtain invertibility of c.
For the cocone equation, substitute the definition of alpha. The adjacent
bridge and inverse bridge cancel. Functoriality reduces the result to the
transition followed by the truncation inclusion being the preceding inclusion.
Iterate this equation p times for p>=0. At p=0 the normalization is the
definition of c; the successor step uses the incoming-alpha recursion.
Integer transports respect these compositions by proof irrelevance. -/
theorem truncation_abutment_cocone
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A)
    (X : BigradedExactCouple B 0)
    (hD : X.D = TruncationCouple.D F K)
    (halpha : (∀ p q : ℤ, X.alpha p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
          eqToHom (by rw [hD]))) :
    ∃ (H : ℤ → B)
        (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
        (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
        (c : ∀ n : ℤ, X.D 0 n ⟶ H n),
        (∀ n q : ℤ, j n q =
          eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
          eqToHom (by rw [hH])) ∧
        (∀ n : ℤ, c n = eqToHom (by congr 1; omega) ≫ j n n) ∧
        (∀ n : ℤ, IsIso (c n)) ∧
        (∀ n p : ℤ,
          X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n - p) =
            eqToHom (by congr 1; omega) ≫ j n (n - (p + 1))) ∧
        (∀ (n p : ℤ) (hp : 0 ≤ p),
          eqToHom (by congr 1 <;> omega) ≫ j n (n - p) =
            X.incomingAlphaIter p.toNat 0 n ≫ c n)  := by
  classical
  let H : ℤ → B := fun n ↦ (DerivedCategory.homologyFunctor B n).obj
    (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj))
  let j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n := fun n q ↦
    eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
      (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q)))
  let c : ∀ n : ℤ, X.D 0 n ⟶ H n := fun n ↦
    eqToHom (by congr 1; omega) ≫ j n n
  refine ⟨H, rfl, j, c, ?_, ?_, ?_, ?_, ?_⟩
  · intro n q; simp only [j, eqToHom_refl, Category.comp_id]
  · intro n; rfl
  · have haux := truncation_abutment_cocone_aux F K X hD halpha H rfl j c
      (by intro n q; dsimp [j]; simp) (by intro n; rfl)
    exact haux.1
  · have haux := truncation_abutment_cocone_aux F K X hD halpha H rfl j c
      (by intro n q; dsimp [j]; simp) (by intro n; rfl)
    exact haux.2.1
  · have haux := truncation_abutment_cocone_aux F K X hD halpha H rfl j c
      (by intro n q; dsimp [j]; simp) (by intro n; rfl)
    exact haux.2.2

end CategoryTheory
