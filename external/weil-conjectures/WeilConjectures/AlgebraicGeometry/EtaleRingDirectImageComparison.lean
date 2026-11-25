/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleRingDirectImageOperations

/-!
# Identifying the ring-object lift of sectionwise etale direct image

Source: Stacks Project, Proposition 00YV, ring paragraph and Section 00YR.
(blueprint: lem-weil-pbc-etale-ring-direct-image-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace AlgebraicGeometry

/-- Source: Stacks Project, Proposition 00YV, ring paragraph; Section 00YR, sextuples.
(blueprint: lem-weil-pbc-etale-ring-direct-image-comparison).

Proof: The forgetful equalities identify the underlying source of the comparison
with R(X), and its target with R of the underlying ring sheaf GU(X). Use their
canonical isomorphisms to define the displayed underlying comparison. The strict
inverse identity GU FU = id transports the five section formulas for FU to GU;
similarly GV FV = id transports the formulas for FV to GV. At every etale object,
the product comparison of R is the coordinate pairing: this follows by composing
with both projections. Its terminal comparison is the unique map between singleton
sections. Substitute these facts in the five RF operation equations. The underlying
comparison then preserves addition, zero, negation, multiplication and one on each
section. Bundle its components and inverse as ring homomorphisms. Naturality follows
from the underlying comparisons, since forgetting ring coefficients is faithful.
Their composites are identities by the underlying isomorphism identities. This
constructs d with exactly the displayed underlying formula. No inverse-image functor,
unit or adjunction is involved in this assertion. -/
theorem etaleRingDirectImageComparison (U V : Scheme.{u}) (f : U ⟶ V)
    (FU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1} ⥤
      CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))))
    (GU : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))) ⥤
      Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (hFU : FU ⋙ CommRingObjCat.forget _ = sheafForget U.smallEtaleTopology)
    (hGU : GU ⋙ sheafForget U.smallEtaleTopology = CommRingObjCat.forget _)
    (hGUFU : GU ⋙ FU = 𝟭 _)
    (opsU : (∀ (A : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (Z : U.Etaleᵒᵖ),
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddMonObj.zero (X := (FU.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FU.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.mul (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.one (X := (FU.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z))))
    (FV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
      CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))))
    (GV : CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))) ⥤
      Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (hFV : FV ⋙ CommRingObjCat.forget _ = sheafForget V.smallEtaleTopology)
    (hGV : GV ⋙ sheafForget V.smallEtaleTopology = CommRingObjCat.forget _)
    (hGVFV : GV ⋙ FV = 𝟭 _)
    (opsV : (∀ (A : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}) (Z : V.Etaleᵒᵖ),
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddMonObj.zero (X := (FV.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FV.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.mul (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.one (X := (FV.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z)))) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∀ (RF : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))) ⥤
          CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))))
      (hRF : RF ⋙ CommRingObjCat.forget _ = CommRingObjCat.forget _ ⋙ R)
      [PreservesFiniteProducts R],
      (∀ X : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))),
            AddMonObj.add (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (eqToIso hRF).hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) →
      ∃ d : RF ⋙ GV ≅ GU ⋙ Rr,
        ∀ X, (sheafForget V.smallEtaleTopology).map (d.hom.app X) =
          (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
            R.map ((eqToIso hGU).inv.app X) := by
  dsimp only
  intro RF hRF hprod opsR
  obtain h := etaleRingDirectImageOperations U V f
    FU GU hFU hGU hGUFU opsU FV GV hFV hGV hGVFV opsV RF hRF opsR
  let α X : (sheafForget V.smallEtaleTopology).obj (GV.obj (RF.obj X)) ⟶
      (sheafForget V.smallEtaleTopology).obj
        (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
          CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale)
          (U.smallGrothendieckTopology @Etale)).obj (GU.obj X)) :=
    (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
        (U.smallGrothendieckTopology @Etale)).map ((eqToIso hGU).inv.app X)
  let dh X : GV.obj (RF.obj X) ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale)
        (U.smallGrothendieckTopology @Etale)).obj (GU.obj X) :=
    ⟨{ app Z := CommRingCat.ofHom
        { toFun := (α X).hom.app Z
          map_zero' := (h X Z).2.1
          map_add' := (h X Z).1
          map_one' := (h X Z).2.2.2
          map_mul' := (h X Z).2.2.1 }
       naturality := by
         intro Z W g
         ext a
         exact ConcreteCategory.congr_hom ((α X).hom.naturality g) a }⟩
  have hh X : (sheafForget V.smallEtaleTopology).map (dh X) = α X := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext Z
    ext a
    rfl
  have hi X : IsIso (dh X) := by
    have hm : IsIso ((sheafForget V.smallEtaleTopology).map (dh X)) := by
      rw [hh]
      dsimp only [α]
      infer_instance
    exact isIso_of_reflects_iso (dh X) (sheafForget V.smallEtaleTopology)
  let d := fun X ↦ @asIso _ _ _ _ (dh X) (hi X)
  have hd X : (sheafForget V.smallEtaleTopology).map (d X).hom =
      (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
          (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
          (U.smallGrothendieckTopology @Etale)).map ((eqToIso hGU).inv.app X) := hh X
  refine ⟨NatIso.ofComponents d ?_, hd⟩
  intro X Y g
  apply (sheafForget V.smallEtaleTopology).map_injective
  simp only [Functor.map_comp, Functor.comp_map]
  rw [hd, hd]
  have hnV := (eqToIso hGV).hom.naturality (RF.map g)
  have hnR := (eqToIso hRF).hom.naturality g
  have hnU := (eqToIso hGU).inv.naturality g
  dsimp only [Functor.comp_map] at hnV hnR hnU
  simp only [Category.assoc]
  rw [← Category.assoc, hnV]
  simp only [Category.assoc]
  rw [← Category.assoc ((CommRingObjCat.forget _).map (RF.map g)), hnR]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  have ht := congrArg
    ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)).map hnU
  exact congrArg (fun k ↦ (eqToIso hGV).hom.app (RF.obj X) ≫
    (eqToIso hRF).hom.app X ≫ k) ht |>.trans (by
      simp only [Functor.map_comp]
      rfl)

end AlgebraicGeometry
