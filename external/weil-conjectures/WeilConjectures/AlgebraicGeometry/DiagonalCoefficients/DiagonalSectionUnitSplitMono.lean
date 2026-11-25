/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # A section splits the canonical derived pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem adj_unit_splitMono
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') [(L ⋙ L').Full] [(L ⋙ L').Faithful]
    (M : C) : IsSplitMono (a.unit.app M) := by
  let adj := a.comp b
  refine ⟨⟨R.map (b.unit.app _) ≫ inv (adj.unit.app M), ?_⟩⟩
  rw [← Category.assoc, ← Adjunction.comp_unit_app a b M, IsIso.hom_inv_id]

private theorem adj_unit_splitMono_of_iso
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ C} {R' : C ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (i : L ⋙ L' ≅ 𝟭 C) (M : C) :
    IsSplitMono (a.unit.app M) := by
  have : (L ⋙ L').Full := Functor.Full.of_iso i.symm
  have : (L ⋙ L').Faithful := Functor.Faithful.of_iso i.symm
  exact adj_unit_splitMono a b M

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar

/-- A scheme section gives a retraction of the twisted derived adjunction unit.

Source: the projective-line unit summand, using the infinity section
(blueprint: lem-diagonal-section-unit-split-mono).

Proof: the composite inverse images along a map and its section are canonically
isomorphic to inverse image along the identity, hence to the identity functor.
The composite adjunction thus has invertible unit. The individual unit followed
by the image of the second unit equals this composite unit, so composing the
image of the second unit with its inverse is a retraction. Postcomposition by
the direct image of the specified endpoint isomorphism preserves split injectivity. -/
theorem diagonalSectionUnit_splitMono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (M : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (e : (derivedUpper Λ f).obj M ≅ N) :
    IsSplitMono ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app M ≫
      (derivedLower Λ f).map e.hom) := by
  let a := CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  let b := CondensedRing.derivedUpperStarLowerStarAdjunction Λ s
  let i : (CondensedRing.upperStar Λ f).leftDerivedFunctor ⋙
      (CondensedRing.upperStar Λ s).leftDerivedFunctor ≅ 𝟭 _ :=
    (CondensedRing.leftDerivedUpperStarComp Λ s f).symm ≪≫
      eqToIso (congrArg (fun g : S ⟶ S ↦ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
        hs) ≪≫ CondensedRing.leftDerivedUpperStarId Λ S
  have : IsSplitMono (a.unit.app M) := adj_unit_splitMono_of_iso a b i M
  change IsSplitMono (a.unit.app M ≫
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor.map e.hom)
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
