/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedBinaryProduct

/-!
# Derived sequence from a sequence exact on injectives

Source: Stacks Project, Tag 0A50, passage from the injective section sequence to
its long exact homology sequence; Homology, Tag 0117.
(blueprint: lem-weil-pbc-right-derived-pair-sequence)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Source: Stacks Project, Tag 0A50, final paragraph, and Homology Tag 0117.
(blueprint: lem-weil-pbc-right-derived-pair-sequence)

Proof: For an injective resolution P of M, evaluate A, B, D, E termwise.
The maps (a,b) and c-d commute with differentials by naturality. Injectivity,
exactness and surjectivity in the hypotheses make the resulting sequence
A(P) → B(P) × D(P) → E(P) degreewise short exact. Apply the homology long
exact sequence. Finite products of abelian groups are exact, so their
complex homology is the product of homologies, with the two projections
identifying the induced maps with (Rⁿa,Rⁿb) and Rⁿc-Rⁿd. Transport by the
canonical isoRightDerivedObj for P. Lift a coefficient morphism to a map of
injective resolutions:
it gives a morphism of the short exact sequences, so naturality of the
homology boundary gives the naturality equation for the transported δ.
Homotopy uniqueness makes this independent of the lift. Taking the
canonical resolutions yields the asserted natural transformations.
Empty and zero categories cause no exception; zero functors and split
sequences give the expected zero boundaries. -/
theorem rightDerived_pair_sequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (A B D E : C ⥤ AddCommGrpCat.{w})
    [A.Additive] [B.Additive] [D.Additive] [E.Additive]
    (a : A ⟶ B) (b : A ⟶ D) (c : B ⟶ E) (d : D ⟶ E)
    (hinj : ∀ (I : C), Injective I →
      Function.Injective (fun x => (a.app I x, b.app I x)))
    (hexact : ∀ (I : C), Injective I →
      Function.Exact (fun x => (a.app I x, b.app I x))
        (fun x => c.app I x.1 - d.app I x.2))
    (hsurj : ∀ (I : C), Injective I →
      Function.Surjective (fun x : B.obj I × D.obj I => c.app I x.1 - d.app I x.2)) :
    ∃ δ : ∀ n : ℕ, E.rightDerived n ⟶ A.rightDerived (n + 1),
      ∀ M : C,
        ∀ n : ℕ,
          Function.Exact (fun x => ((a.rightDerived n).app M x,
            (b.rightDerived n).app M x))
            (fun x => (c.rightDerived n).app M x.1 - (d.rightDerived n).app M x.2) ∧
          Function.Exact
            (fun x : (B.rightDerived n).obj M × (D.rightDerived n).obj M =>
              (c.rightDerived n).app M x.1 - (d.rightDerived n).app M x.2)
            ((δ n).app M) ∧
          Function.Exact ((δ n).app M)
            (fun x => ((a.rightDerived (n + 1)).app M x,
              (b.rightDerived (n + 1)).app M x)) := by
  obtain ⟨δ, hδ⟩ := rightDerived_injective_sequence A (abBinaryProduct B D) E
    (abBinaryProductLift a b) (abBinaryProductDifference c d) hinj hexact hsurj
  refine ⟨δ, ?_⟩
  intro M n
  obtain ⟨e, he₁, he₂⟩ := rightDerived_binaryProduct_iso A B D E a b c d M n
  obtain ⟨e', he'₁, _⟩ := rightDerived_binaryProduct_iso A B D E a b c d M (n + 1)
  obtain ⟨h₁, h₂, h₃⟩ := hδ M n
  have bij := ConcreteCategory.bijective_of_isIso e.hom
  have inj' := (ConcreteCategory.bijective_of_isIso e'.hom).1
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := bij.2 y
    dsimp only
    rw [← he₂, h₁]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, (he₁ z).symm⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, bij.1 ((he₁ z).trans hz)⟩
  · intro y
    rw [h₂]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.hom x, (he₂ x).symm⟩
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := bij.2 x
      exact ⟨z, (he₂ z).trans hx⟩
  · intro y
    dsimp only
    rw [← he'₁, ← map_zero e'.hom.hom, inj'.eq_iff, h₃]

end CategoryTheory
