/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! Transport of commutative ring objects along finite-product-preserving functors. -/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction


/-- The usual monoidal transports of the operations satisfy the ring laws. -/
private abbrev transportedRing
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B] [BraidedCategory B]
    (F : A ⥤ B) [F.Braided] (X : A) [CommRingObj X] : CommRingObj (F.obj X) where
  __ := F.addGrpObjObj
  add_comm := by
    dsimp
    rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp,
      IsCommAddMonObj.add_comm]
  __ := F.monObjObj X
  __ := F.isCommMonObj_obj
  mul_add := by
    rw [← cancel_epi ((Functor.Monoidal.μIso F X (X ⊗ X)).inv ≫
      (𝟙 (F.obj X) ⊗ₘ (Functor.Monoidal.μIso F X X).inv))]
    simp only [Category.assoc]
    dsimp only [Functor.Monoidal.μIso]
    simp only [Functor.obj.σ_def, Functor.obj.μ_def]
    simp only [whiskerLeft_comp, Category.assoc]
    simp only [id_tensorHom,
      comp_lift_assoc, ← whiskerLeft_comp_assoc,
      Functor.OplaxMonoidal.δ_fst, Functor.OplaxMonoidal.δ_snd,
      Functor.OplaxMonoidal.δ_natural_right_assoc,
      Functor.Monoidal.δ_μ_assoc, ← Functor.OplaxMonoidal.lift_δ_assoc,
      ← F.map_comp]
    exact congrArg F.map (RingObj.mul_add X)

  add_mul := by
    rw [← cancel_epi ((Functor.Monoidal.μIso F (X ⊗ X) X).inv ≫
      ((Functor.Monoidal.μIso F X X).inv ⊗ₘ 𝟙 (F.obj X)))]
    simp only [Category.assoc]
    dsimp only [Functor.Monoidal.μIso]
    simp only [Functor.obj.σ_def, Functor.obj.μ_def]
    simp only [comp_whiskerRight, Category.assoc]
    simp only [tensorHom_id,
      comp_lift_assoc, ← comp_whiskerRight_assoc,
      Functor.OplaxMonoidal.δ_fst, Functor.OplaxMonoidal.δ_snd,
      Functor.OplaxMonoidal.δ_natural_left_assoc,
      Functor.Monoidal.δ_μ_assoc, ← Functor.OplaxMonoidal.lift_δ_assoc,
      ← F.map_comp]
    exact congrArg F.map (RingObj.add_mul X)


/-- Transport of a single finite-product-preserving functor on commutative ring objects.
(blueprint: lem-weil-pbc-finite-product-ring-functor)
Source: Stacks Project, Proposition 00YV, paragraph on rings as sextuples.

Proof: on an object X take the underlying object F(X). Define addition and
multiplication by F of the original binary operation precomposed with the inverse
product comparison, zero and one using the inverse terminal comparison, and
negation by F of negation. For any term in n variables, its transported evaluation
composed with the comparison F(X^n) -> F(X)^n equals F of its original evaluation.
Prove this by induction: projections follow from the defining comparison;
constants follow from uniqueness of maps to the terminal object; operations follow
from naturality of binary comparisons and functoriality. Applying this identity to
both sides of associativity, units, inverses, commutativity and distributivity and
cancelling the comparison proves all CommRingObj axioms. Send a ring morphism f to
F(f). Naturality of the comparisons proves preservation of addition, multiplication,
zero and one; negation follows from the additive group structure. Functoriality
follows from that of F. The underlying objects and maps were chosen literally as
F(X) and F(f), so the forgetful equality holds strictly. Its eqToIso components
are identities, giving the displayed operation equations. -/
theorem finiteProductRingFunctor
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    (F : A ⥤ B) [PreservesFiniteProducts F] :
    letI : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    letI : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    ∃ (FF : CommRingObjCat A ⥤ CommRingObjCat B)
      (hF : FF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ F),
      let eF := eqToIso hF
      (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (FF.obj X).X) ≫ eF.hom.app X =
              (eF.hom.app X ⊗ₘ eF.hom.app X) ≫
                (prodComparisonIso F X.X X.X).inv ≫ F.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (FF.obj X).X) ≫ eF.hom.app X =
              (preservesTerminalIso F).inv ≫ F.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (FF.obj X).X) ≫ eF.hom.app X =
              eF.hom.app X ≫ F.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (FF.obj X).X) ≫ eF.hom.app X =
              (eF.hom.app X ⊗ₘ eF.hom.app X) ≫
                (prodComparisonIso F X.X X.X).inv ≫ F.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (FF.obj X).X) ≫ eF.hom.app X =
              (preservesTerminalIso F).inv ≫ F.map (MonObj.one (X := X.X))) := by
  let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
  let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  let FF : CommRingObjCat A ⥤ CommRingObjCat B :=
    { obj X := { X := F.obj X.X, commRingObj := transportedRing F X.X }
      map {X Y} f := by
        let : AddMonObj (F.obj X.X) := F.addMonObjObj X.X
        let : AddMonObj (F.obj Y.X) := F.addMonObjObj Y.X
        let : MonObj (F.obj X.X) := F.monObjObj X.X
        let : MonObj (F.obj Y.X) := F.monObjObj Y.X
        exact
          { hom := F.map f.hom
            isRingHom :=
              { toIsAddMonHom := Functor.map.instIsAddMonHom (F := F) X.X Y.X f.hom
                toIsMonHom := Functor.map.instIsMonHom (F := F) X.X Y.X f.hom } }
      map_id X := CommRingObjCat.hom_ext (F.map_id X.X)
      map_comp f g := CommRingObjCat.hom_ext (F.map_comp f.hom g.hom) }
  have hF : FF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ F := rfl
  refine ⟨FF, hF, ?_⟩
  dsimp only
  intro X
  simp [FF, CommRingObjCat.forget, Functor.Monoidal.μ_of_cartesianMonoidalCategory,
    Functor.Monoidal.ε_of_cartesianMonoidalCategory]

end CategoryTheory.Adjunction
