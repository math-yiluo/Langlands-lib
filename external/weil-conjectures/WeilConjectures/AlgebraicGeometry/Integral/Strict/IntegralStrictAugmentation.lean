/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections

import WeilConjectures.CategoryTheory.Augmented.AugmentedDerivedTowerUnit

/-! # The canonical augmentation of a simultaneous integral reduction

The construction uses the universal left-derived counit and localization, so its
naturality holds for all derived morphisms.

## References

* Stacks 099M, canonical completion-map construction
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a v w s
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The simultaneous quotient projections form one map of strict towers. -/
def diagonalReductionTowerAugmentation
    {A : Type a} [Category.{v} A] [Abelian A] (ℓ : ℕ)
    (O : DiagonalReductionPresentation ℓ (𝟭 A)) : Functor.const ℕᵒᵖ ⟶ O.E where
  app M := NatTrans.ofOpSequence (fun n ↦ (O.π n).app M) (fun n ↦ by
    change 𝟙 M ≫ (O.π n).app M = _
    simpa only [Category.id_comp] using (O.transition n M).symm)
  naturality M N f := by
    ext n
    exact (O.π n.unop).naturality f

section Augmentation

variable {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{s} (ℕᵒᵖ ⥤ A)]

variable (ℓ : ℕ) (I : DiagonalDerivedReduction ℓ (𝟭 A))
  (RZ : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
  (ηZ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)

/-- The ordinary quotient map followed by the specified derived-limit comparison.
This construction uses no left-derived reduction. -/
def integralStrictOrdinaryAugmentation
    (O : DiagonalReductionPresentation ℓ (𝟭 A)) (P : CochainComplex A ℤ) :
    DerivedCategory.Q.obj P ⟶
      RZ.obj (DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P)) :=
  DerivedCategory.Q.map
      (((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapHomologicalComplex
          (.up ℤ)).unit.app P ≫
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (diagonalReductionTowerAugmentation ℓ O) (.up ℤ)).app P)) ≫
      ηZ.app ((O.E.mapHomologicalComplex (.up ℤ)).obj P)

/-- A natural map into the derived strict quotient limit, with its ordinary normalization.
The two universal lifts are supplied by the existing generic augmented-tower theorem. -/
theorem exists_integralStrictAugmentation :
    ∃ a : 𝟭 (DerivedCategory A) ⟶ I.T ⋙ RZ,
      ∀ P : CochainComplex A ℤ,
        a.app (DerivedCategory.Q.obj P) ≫ RZ.map (I.ε.app P) =
          integralStrictOrdinaryAugmentation ℓ RZ ηZ I.ordinary P := by
  have := I.universal
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension I.T I.ε
    (HomologicalComplex.quasiIso A (.up ℤ))
  obtain ⟨t, v, _, _, _, _, hfac⟩ := exists_augmentedDerivedTowerUnit
    (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
    ((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ))
    (I.ordinary.E.mapHomologicalComplex (.up ℤ))
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ))
    (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory I.T RZ
    ((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).unit
    (NatTrans.mapHomologicalComplex (diagonalReductionTowerAugmentation ℓ I.ordinary)
      (.up ℤ)) ηZ (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors I.ε
  exact ⟨v ≫ Functor.whiskerRight t RZ, hfac⟩

end Augmentation
end AlgebraicGeometry.ProEtale
