/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageCompletionAugmentationCoherence
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageCompletionConstantMateIso

/-! # Completion augmentation square for direct image

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, (3): the completion map
is induced by `c(N) → red(N)` and the direct image of this augmentation
(blueprint: lem-weil-pbc-direct-image-completion-unit-square).

The reduction/direct-image comparison `h` is written as the adjunction mate of the
canonical pullback/reduction comparison `pullReduction`. This is verbatim the body of
`pushReductionMap` of `proposition-proper-base-change-complete-integral--1`. That node's proof uses
the present lemma, so this module does not import its module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Naturality of mates transports a commuting inverse-image square to its direct-image
mate square. -/
private theorem mate_naturality_general
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {K : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (α : G ⋙ K ⟶ F ⋙ H) (β : G' ⋙ K ⟶ F ⋙ H')
    (pG : G ⟶ G') (pH : H ⟶ H')
    (hc : ∀ X, K.map (pG.app X) ≫ β.app X =
      α.app X ≫ pH.app (F.obj X)) (N : B) :
    pG.app (R.obj N) ≫
        (mateEquiv a b (TwoSquare.mk _ _ _ _ β)).app N =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).app N ≫
        S.map (pH.app N) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hα := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ α) N
  have hβ := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ β) N
  have hn := b.counit.naturality (pH.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hpn := pH.naturality (a.counit.app N)
  dsimp only [Functor.comp_obj] at hpn
  rw [hβ]
  dsimp only [TwoSquare.mk]
  have hhc := hc (R.obj N)
  rw [← Category.assoc]
  rw [hhc]
  simp only [Category.assoc]
  rw [← hpn]
  rw [← Category.assoc, hn]
  rw [← hα]
  simp only [Functor.id_obj]
  change (K.map (((mateEquiv a b) (TwoSquare.mk G F K H α)).app N) ≫
      b.counit.app (H.obj N)) ≫ pH.app N =
    K.map (((mateEquiv a b) (TwoSquare.mk G F K H α)).app N) ≫
      b.counit.app (H.obj N) ≫ pH.app N
  simp only [Category.assoc]

/-- Direct image carries the completion augmentation through the canonical constant-tower
comparison. The comparison `χ` is the mate of the constant/pullback interchange, and the
second edge is the mate of `pullReduction`.

Proof steps:
1. Use `directImage_constant_mate_isIso` to obtain the isomorphism `χ` from the
   constant-tower mate.
2. Apply `directImage_augmentation_pullReduction_coherence` to the underlying
   pullback/reduction square.
3. Apply the local mate naturality calculation to this commuting square; its counit
   identities give the displayed equality at every derived object.
(blueprint: lem-weil-pbc-direct-image-completion-unit-square) -/
theorem directImageCompletionUnitSquare :
    ∃ χ : rpushModule l E f ⋙ dconstant l E Y ≅ dconstant l E X ⋙ rpush l E f,
      χ.hom = (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
        (.mk _ _ _ _ (constantInterchange l E
          (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv)) ∧
      ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
        (augmentation l E Y).app ((rpushModule l E f).obj K) ≫
            ((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
              (.mk _ _ _ _ (pullReduction l E f).hom))).app K =
          χ.hom.app K ≫ (rpush l E f).map ((augmentation l E X).app K) := by
  let χ := (mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
    (.mk _ _ _ _ (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv))
  have : IsIso χ := directImage_constant_mate_isIso l E f
  refine ⟨asIso χ, rfl, ?_⟩
  intro K
  apply mate_naturality_general (moduleAdjunction l E f) (towerAdjunction l E f)
    (α := (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv)
    (β := (pullReduction l E f).hom)
    (pG := augmentation l E Y) (pH := augmentation l E X)
    (hc := fun M ↦ directImage_augmentation_pullReduction_coherence l E f M) (N := K)

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
