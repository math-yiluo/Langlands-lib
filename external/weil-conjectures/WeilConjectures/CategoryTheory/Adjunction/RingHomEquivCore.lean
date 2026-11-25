/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Adjunction.RingAdjunctPreservesOperations
import WeilConjectures.CategoryTheory.Adjunction.RingCoadjunctPreservesOperations

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

/-- Restriction of the original natural hom-bijection to ring morphisms, once the
transported functors and their operation equations have been constructed.
(blueprint: lem-weil-pbc-ring-hom-equiv-core)
Source: Stacks Project, Proposition 00YV, proof of (2), details of adjunct restriction.

Proof: identify the underlying objects using hL and hR. Naturality of the unit
on each product projection gives its compatibility with the binary comparisons:
if lambda : L(X x X) -> LX x LX and rho : R(LX x LX) -> RLX x RLX
are the comparisons, then rho o R(lambda) o eta_(X x X) = eta_X x eta_X.
Both sides have projections eta_X o pr_k by naturality. Dually,
epsilon_(Y x Y) o L(rho^(-1)) = (epsilon_Y x epsilon_Y) o lambda_(RY,RY),
as follows from counit naturality after checking the two projections.
Naturality at addition and multiplication, followed by the given
operation equations, makes the unit preserve both binary operations. At zero and
one use naturality and uniqueness of maps into the terminal object; negation
uses naturality directly. Dually the counit preserves the five operations by
checking the comparison identity on each product projection. Thus the adjunct
of a ring morphism is a ring morphism, since it is its R-image composed with the
unit; the inverse adjunct is a ring morphism, since it is its L-image followed
by the counit. The original adjunction identities prove the two maps inverse.
The original naturality equalities restrict to ring morphisms because the lifted
functors have the specified underlying maps. This is a CoreHomEquiv. Its forward
formula is the original adjunct, conjugated by eL and eR. Evaluating on identity
morphisms gives the unit and counit formulas, cancelling inverse comparisons.
This proof works for any braided structures in which the supplied ring objects
exist; only their given operation equations and Cartesian products are used. -/
theorem ringHomEquivCore
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    [BraidedCategory A] [BraidedCategory B]
    (LF : CommRingObjCat A ⥤ CommRingObjCat B) (RF : CommRingObjCat B ⥤ CommRingObjCat A)
    (hL : LF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ L)
    (hR : RF ⋙ CommRingObjCat.forget A = CommRingObjCat.forget B ⋙ R)
    (opsL : let eL := eqToIso hL; (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X))))
    (opsR : let eR := eqToIso hR; (∀ X : CommRingObjCat B,
            AddMonObj.add (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)))) :
    let eL := eqToIso hL
    let eR := eqToIso hR
    ∃ c : Adjunction.CoreHomEquiv LF RF,
      (∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y),
        (CommRingObjCat.forget A).map (c.homEquiv X Y f) ≫ eR.hom.app Y =
          adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommRingObjCat.forget B).map f)) ∧
      (∀ X : CommRingObjCat A,
        (CommRingObjCat.forget A).map (c.homEquiv X (LF.obj X) (𝟙 _)) ≫
          eR.hom.app (LF.obj X) ≫ R.map (eL.hom.app X) = adj.unit.app X.X) ∧
      (∀ Y : CommRingObjCat B,
        L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
          (CommRingObjCat.forget B).map ((c.homEquiv (RF.obj Y) Y).symm (𝟙 _)) =
            adj.counit.app Y.X) := by
  set_option backward.defeqAttrib.useBackward true in
    let eL := eqToIso hL
    let eR := eqToIso hR
    have hf := ringAdjunctPreservesOperations adj LF RF hL hR opsL opsR
    have hg := ringCoadjunctPreservesOperations adj LF RF hL hR opsL opsR
    let E : ∀ X Y, (LF.obj X ⟶ Y) ≃ (X ⟶ RF.obj Y) := fun X Y ↦
      { toFun := fun f ↦ CommRingObjCat.Hom.mk (adj.homEquiv X.X Y.X (eL.inv.app X ≫ f.hom) ≫
            eR.inv.app Y) (isRingHom := hf X Y f)
        invFun := fun g ↦ CommRingObjCat.Hom.mk (eL.hom.app X ≫
            (adj.homEquiv X.X Y.X).symm (g.hom ≫ eR.hom.app Y)) (isRingHom := hg X Y g)
        left_inv := fun f ↦ by
          apply CommRingObjCat.hom_ext
          dsimp
          simp [Category.assoc, eL, eR]
        right_inv := fun g ↦ by
          apply CommRingObjCat.hom_ext
          dsimp
          simp [Category.assoc, eL, eR] }
    let c : Adjunction.CoreHomEquiv LF RF :=
      { homEquiv := E
        homEquiv_naturality_left_symm := by
          intro X' X Y f g
          apply CommRingObjCat.hom_ext
          change eL.hom.app X' ≫ (adj.homEquiv _ _).symm
              ((f.hom ≫ g.hom) ≫ eR.hom.app Y) =
            (LF.map f).hom ≫ eL.hom.app X ≫
              (adj.homEquiv _ _).symm (g.hom ≫ eR.hom.app Y)
          rw [Category.assoc, adj.homEquiv_naturality_left_symm]
          simpa only [Category.assoc, Functor.comp_map, CommRingObjCat.forget_map,
            CommRingObjCat.forget_obj] using
            congrArg (fun t ↦ t ≫ (adj.homEquiv _ _).symm (g.hom ≫ eR.hom.app Y))
              (eL.hom.naturality f).symm
        homEquiv_naturality_right := by
          intro X Y Y' f g
          apply CommRingObjCat.hom_ext
          change adj.homEquiv _ _ (eL.inv.app X ≫ (f.hom ≫ g.hom)) ≫
              eR.inv.app Y' =
            (adj.homEquiv _ _ (eL.inv.app X ≫ f.hom) ≫ eR.inv.app Y) ≫ (RF.map g).hom
          rw [← Category.assoc, adj.homEquiv_naturality_right]
          simpa only [Category.assoc, Functor.comp_map, CommRingObjCat.forget_map,
            CommRingObjCat.forget_obj] using
            congrArg (fun t ↦ adj.homEquiv _ _ (eL.inv.app X ≫ f.hom) ≫ t)
              (eR.inv.naturality g) }
    refine ⟨c, ?_, ?_, ?_⟩
    · intro X Y f
      change (adj.homEquiv _ _ _ ≫ eR.inv.app Y) ≫ eR.hom.app Y = _
      simp [Category.assoc, eL, eR]
    · intro X
      change (adj.homEquiv _ _ (eL.inv.app X ≫ 𝟙 _) ≫ eR.inv.app _) ≫
        eR.hom.app _ ≫ R.map (eL.hom.app X) = _
      simp [Category.assoc, adj.homEquiv_unit, ← R.map_comp, eL, eR]
    · intro Y
      change L.map (eR.inv.app Y) ≫ eL.inv.app _ ≫
        (eL.hom.app _ ≫ (adj.homEquiv _ _).symm (𝟙 _ ≫ eR.hom.app Y)) = _
      simp [adj.homEquiv_counit, eL, eR]

end CategoryTheory.Adjunction
