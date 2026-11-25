/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections

/-! Uniqueness for the normalized ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] completed derivedExtension SheafOfModules.monoidalCategory
  strictLimit ordinaryUnit quotientPresentation
attribute [local irreducible] derivedPull

private def finiteScalarAdj {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {R S : Sheaf K CommRingCat.{u}} (c : R ⟶ S) :
    change c ⊣ res c :=
  SheafOfModules.RingedTensor.tensorAdjunction c

private theorem finiteInsertion_eq_unit {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {R S : Sheaf K CommRingCat.{u}} (c : R ⟶ S)
    (M : Mod R) :
    insertion c M = (underlying R).map ((finiteScalarAdj c).unit.app M) := by
  apply (insertion_existsUnique c M).unique
    (insertion_existsUnique c M).exists.choose_spec
  intro U m
  rfl

private theorem finiteScalar_homEquiv {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {R S : Sheaf K CommRingCat.{u}} (c : R ⟶ S)
    (M : Mod R) (N : Mod S) (f : (change c).obj M ⟶ N) :
    (underlying R).map ((finiteScalarAdj c).homEquiv _ _ f) =
      insertion c M ≫ (underlying S).map f := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, finiteInsertion_eq_unit]
  rfl

omit hL in
private theorem finitePull_homEquiv {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S)
    (M : Mod R) (N : Mod S) (f : (pull F c).obj M ⟶ N) :
    (F.algebra R).moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj R)).map ((finiteScalarAdj c).homEquiv _ _ f) =
      pullInsertion F c M ≫ (underlying S).map f := by
  rw [finiteScalar_homEquiv, pullInsertion, Category.assoc]

include V adj hL in
/-- Two isomorphisms satisfying the insertion normalization are equal.
Source: Stacks Project, Tags 06YY and 099L.
(auxiliary; not a blueprint node).
The insertion maps generate the sheafified scalar extensions, so the displayed
formula determines every component and hence the natural isomorphism. -/
theorem ordinaryFinitePull_unique
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e e' : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))))
    (he : ∀ M : Mod (constant J A),
      pullInsertion F (constantMap F A) M ≫
          insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
          (underlying (finite J' A I n)).map (e.hom.app M) =
        L.map (insertion (quotient J A I n) M) ≫
          pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
            ((change (quotient J A I n)).obj M))
    (he' : ∀ M : Mod (constant J A),
      pullInsertion F (constantMap F A) M ≫
          insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
          (underlying (finite J' A I n)).map (e'.hom.app M) =
        L.map (insertion (quotient J A I n) M) ≫
          pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
            ((change (quotient J A I n)).obj M)) : e = e' := by
  have _ := adj
  have _ := hL
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((finiteScalarAdj (quotient J' A I n)).homEquiv _ _).injective
  apply ((finiteScalarAdj (constantMap F A)).homEquiv _ _).injective
  apply (underlying (F.rings.obj (constant J A))).map_injective
  apply (cancel_epi ((F.algebra (constant J A)).moduleUnderlying.inv.app M)).mp
  rw [finitePull_homEquiv, finitePull_homEquiv,
    finiteScalar_homEquiv, finiteScalar_homEquiv]
  exact (he M).trans (he' M).symm
end CategoryTheory.ConstantCompletion
