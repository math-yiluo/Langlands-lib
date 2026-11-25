/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerExtraction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The canonical algebraic quotient diagram and compatible markings

Source: Stacks Project, Tag 09C6 and More on Algebra, Tag 09AW.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The canonical consecutive quotient map, obtained by transposing the level unit.
Source: Stacks Tag 09AW.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-diagram). -/
def finitePerfectAdicQuotientTransition
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{t} A)) (n : ℕ) :
    (L (n + 1)).obj C ⟶
      (DerivedCategory.adicStepRestriction I n).obj ((L n).obj C) :=
  ((adj (n + 1)).homEquiv C _).symm
    ((adj n).unit.app C ≫ (DerivedCategory.adicRestrictionComp I n).hom.app ((L n).obj C))

/-- The actual algebraic quotient diagram of a specified complex.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-diagram). -/
def finitePerfectAdicQuotientDiagram
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{t} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{t} A) :=
  Functor.ofOpSequence (X := fun n ↦
    (DerivedCategory.adicLevelRestriction I n).obj ((L n).obj C))
    (DerivedCategory.adicTowerTransition I (fun n ↦ (L n).obj C)
      (finitePerfectAdicQuotientTransition I L adj C))

private theorem quotientTransition_unit
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{t} A)) (n : ℕ) :
    (adj (n + 1)).unit.app C ≫
        (DerivedCategory.adicLevelRestriction I (n + 1)).map
          (finitePerfectAdicQuotientTransition I L adj C n) =
      (adj n).unit.app C ≫
        (DerivedCategory.adicRestrictionComp I n).hom.app ((L n).obj C) := by
  exact ((adj (n + 1)).homEquiv C _).apply_symm_apply _

/-- Compatible level markings identify the entire diagram with the canonical quotient diagram.

Source: Stacks Project, Tag 09C6, compatibility with the actual quotient transitions;
More on Algebra, Tag 09AW.
(blueprint: lem-weil-pbc-finite-perfect-adic-quotient-diagram).

Proof: transpose each proposed consecutive square under the (n+1)-st adjunction.
Its two transposes agree by the given unit equation and naturality of iterated
scalar restriction. Injectivity of the adjunction Hom bijection gives that square.
The level isomorphisms then define an isomorphism of sequential diagrams: consecutive
naturality implies naturality for all composites, including identity transitions. -/
theorem finitePerfectAdicQuotientDiagram_marking
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{t} A))
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (v : ∀ n : ℕ, K (n + 1) ⟶ (DerivedCategory.adicStepRestriction I n).obj (K n))
    (e : ∀ n : ℕ, (L n).obj C ≅ K n)
    (he : ∀ n : ℕ,
      (adj (n + 1)).unit.app C ≫
          (DerivedCategory.adicLevelRestriction I (n + 1)).map (e (n + 1)).hom ≫
          DerivedCategory.adicTowerTransition I K v n =
        (adj n).unit.app C ≫
          (DerivedCategory.adicLevelRestriction I n).map (e n).hom) :
    Nonempty (finitePerfectAdicQuotientDiagram I L adj C ≅
      Functor.ofOpSequence (X := fun n ↦
        (DerivedCategory.adicLevelRestriction I n).obj (K n))
        (DerivedCategory.adicTowerTransition I K v)) := by
  classical
  have hv (n : ℕ) : (e (n + 1)).hom ≫ v n =
      finitePerfectAdicQuotientTransition I L adj C n ≫
        (DerivedCategory.adicStepRestriction I n).map (e n).hom := by
    apply ((adj (n + 1)).homEquiv C _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    apply (cancel_mono ((DerivedCategory.adicRestrictionComp I n).inv.app (K n))).1
    simp only [Category.assoc]
    rw [reassoc_of% quotientTransition_unit I L adj C n]
    have hn := (DerivedCategory.adicRestrictionComp I n).inv.naturality (e n).hom
    simp only [Functor.comp_map] at hn
    rw [hn, Iso.hom_inv_id_app_assoc]
    simpa only [DerivedCategory.adicTowerTransition, Category.assoc] using he n
  let α : finitePerfectAdicQuotientDiagram I L adj C ⟶
      Functor.ofOpSequence (X := fun n ↦
        (DerivedCategory.adicLevelRestriction I n).obj (K n))
        (DerivedCategory.adicTowerTransition I K v) :=
    NatTrans.ofOpSequence (fun n ↦
      (DerivedCategory.adicLevelRestriction I n).map (e n).hom) (by
        intro n
        dsimp only [finitePerfectAdicQuotientDiagram]
        simp only [Functor.ofOpSequence_map_homOfLE_succ,
          DerivedCategory.adicTowerTransition]
        rw [← Category.assoc, ← Functor.map_comp, hv, Functor.map_comp]
        have h := (DerivedCategory.adicRestrictionComp I n).inv.naturality (e n).hom
        simpa only [Category.assoc, Functor.comp_map] using
          congrArg (fun q ↦ (DerivedCategory.adicLevelRestriction I (n + 1)).map
            (finitePerfectAdicQuotientTransition I L adj C n) ≫ q) h.symm)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := by
    change IsIso ((DerivedCategory.adicLevelRestriction I n.unop).map (e n.unop).hom)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α⟩

end AlgebraicGeometry.Scheme
