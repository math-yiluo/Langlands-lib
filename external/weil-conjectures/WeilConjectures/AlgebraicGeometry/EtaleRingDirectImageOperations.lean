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

/-!
# Identifying the ring-object lift of sectionwise etale direct image

Source: Stacks Project, Proposition 00YV, ring paragraph and Section 00YR.
(blueprint: lem-weil-pbc-etale-ring-direct-image-operations).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace AlgebraicGeometry

/-- Source: Stacks Project, Proposition 00YV, ring paragraph; equality transport in
step 1 of (blueprint: lem-weil-pbc-etale-ring-direct-image-operations).
Equality of bundled internal rings transports the operations as well as the carrier.
After eliminating that equality, the two carrier identifications agree by proof irrelevance. -/
private theorem transportSectionOperations.{v, w} {C : Type v} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget CommRingCat.{w})]
    (A : Sheaf J CommRingCat.{w}) (Y X : CommRingObjCat (Sheaf J (Type w)))
    (p : Y = X) (h : Y.X = (sheafForget J).obj A)
    (k : (sheafForget J).obj A = X.X) (Z : Cᵒᵖ)
    (ops :
      (∀ a b, (eqToHom h).hom.app Z
        ((AddMonObj.add (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((AddMonObj.zero (X := Y.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom h).hom.app Z ((MonObj.mul (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((MonObj.one (X := Y.X)).hom.app Z t) =
        (1 : A.obj.obj Z))) :
      (∀ a b, (eqToHom k.symm).hom.app Z
        ((AddMonObj.add (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((AddMonObj.zero (X := X.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom k.symm).hom.app Z ((MonObj.mul (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((MonObj.one (X := X.X)).hom.app Z t) =
        (1 : A.obj.obj Z)) := by
  cases p
  exact ops

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Proposition 00YV, ring paragraph; Section 00YR, sextuples.
(blueprint: lem-weil-pbc-etale-ring-direct-image-operations).

Proof: Fix X and an etale object Z. For any internal ring Y on either site,
apply the supplied section formulas to GY. The equality G F = id identifies
F(GY) with Y as an internal ring, hence identifies all its operations.
The forgetful equalities make the composite of the resulting underlying
identifications the identity. Thus the inverse of eG carries the internal
addition, zero, multiplication and one to the corresponding section operations
of GY. For sectionwise direct image R, the inverse product comparison sends a
pair of sections to that same pair at the base-changed object: compose with the
two projections to check this assertion. The inverse terminal comparison sends
the unique singleton section to the unique singleton section. Evaluate each of
the supplied RF addition, zero, multiplication and one equations at Z, and apply
these product and terminal descriptions. Finally use the preceding operation
identifications for GU and GV. The four resulting equations are exactly the
four assertions for c. This calculation is valid for the zero ring and requires
no points or nonempty sections. It asserts only preservation of operations;
constructing ring homomorphisms, proving invertibility and proving naturality
are separate steps handled by the importing module. -/
theorem etaleRingDirectImageOperations (U V : Scheme.{u}) (f : U ⟶ V)
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
      ∀ X (Z : V.Etaleᵒᵖ),
        let c : (GV.obj (RF.obj X)).obj.obj Z → (Rr.obj (GU.obj X)).obj.obj Z :=
          ((eqToIso hGV).hom.app (RF.obj X) ≫
          (eqToIso hRF).hom.app X ≫ R.map ((eqToIso hGU).inv.app X)).hom.app Z
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a + b) = c a + c b) ∧
        c (0 : (GV.obj (RF.obj X)).obj.obj Z) = 0 ∧
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a * b) = c a * c b) ∧
        c (1 : (GV.obj (RF.obj X)).obj.obj Z) = 1 := by
  dsimp only
  intro RF hRF _ hOps X Z
  have hu (W : U.Etaleᵒᵖ) := transportSectionOperations (GU.obj X)
    (FU.obj (GU.obj X)) X (Functor.congr_obj hGUFU X)
    (Functor.congr_obj hFU (GU.obj X)) (Functor.congr_obj hGU X) W
    (by
      have hh := opsU (GU.obj X) W
      simp only [eqToIso.hom, eqToHom_app] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩)
  have hv := transportSectionOperations (GV.obj (RF.obj X))
    (FV.obj (GV.obj (RF.obj X))) (RF.obj X) (Functor.congr_obj hGVFV (RF.obj X))
    (Functor.congr_obj hFV (GV.obj (RF.obj X))) (Functor.congr_obj hGV (RF.obj X)) Z
    (by
      have hh := opsV (GV.obj (RF.obj X)) Z
      simp only [eqToIso.hom, eqToHom_app] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩)
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let eU := (eqToIso hGU).app X
  let eV := (eqToIso hGV).app (RF.obj X)
  let eR := (eqToIso hRF).app X
  have kU : eU.inv = eqToHom (Functor.congr_obj hGU X).symm := by
    change (eqToIso hGU).inv.app X = _
    rw [eqToIso.inv, eqToHom_app]
  have kV : eV.inv = eqToHom (Functor.congr_obj hGV (RF.obj X)).symm := by
    change (eqToIso hGV).inv.app (RF.obj X) = _
    rw [eqToIso.inv, eqToHom_app]
  have hu' := hu (b.op.obj Z)
  rw [← kU] at hu'
  rw [← kV] at hv
  have hprod (a d : (R.obj X.X).obj.obj Z) :
      (prodComparisonIso R X.X X.X).inv.hom.app Z (a, d) = (a, d) := by
    have hf : (prodComparisonIso R X.X X.X).inv ≫ R.map (fst X.X X.X) =
        fst (R.obj X.X) (R.obj X.X) := by
      apply (prodComparisonIso R X.X X.X).inv_comp_eq.mpr
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst]
    have hs : (prodComparisonIso R X.X X.X).inv ≫ R.map (snd X.X X.X) =
        snd (R.obj X.X) (R.obj X.X) := by
      apply (prodComparisonIso R X.X X.X).inv_comp_eq.mpr
      simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd]
    apply Prod.ext
    · exact congrArg (fun g => g.hom.app Z (a, d)) hf
    · exact congrArg (fun g => g.hom.app Z (a, d)) hs
  have hVI (a : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.inv.hom.app Z (eV.hom.hom.app Z a) = a :=
    congrArg (fun g => g.hom.app Z a) eV.hom_inv_id
  have hVH (a : (RF.obj X).X.obj.obj Z) :
      eV.hom.hom.app Z (eV.inv.hom.app Z a) = a :=
    congrArg (fun g => g.hom.app Z a) eV.inv_hom_id
  have hinj {a d : (RF.obj X).X.obj.obj Z}
      (h : eV.inv.hom.app Z a = eV.inv.hom.app Z d) : a = d := by
    have hh := congrArg (fun x => eV.hom.hom.app Z x) h
    simpa only [hVH] using hh
  have hvadd (a d : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.hom.hom.app Z (a + d) =
        (AddMonObj.add (X := (RF.obj X).X)).hom.app Z
          (eV.hom.hom.app Z a, eV.hom.hom.app Z d) := by
    apply hinj
    exact (hVI (a + d)).trans
      ((hv.1 (eV.hom.hom.app Z a) (eV.hom.hom.app Z d)).trans
        (congrArg₂ (fun x y : (GV.obj (RF.obj X)).obj.obj Z => x + y)
          (hVI a) (hVI d))).symm
  have hvmul (a d : (GV.obj (RF.obj X)).obj.obj Z) :
      eV.hom.hom.app Z (a * d) =
        (MonObj.mul (X := (RF.obj X).X)).hom.app Z
          (eV.hom.hom.app Z a, eV.hom.hom.app Z d) := by
    apply hinj
    exact (hVI (a * d)).trans
      ((hv.2.2.1 (eV.hom.hom.app Z a) (eV.hom.hom.app Z d)).trans
        (congrArg₂ (fun x y : (GV.obj (RF.obj X)).obj.obj Z => x * y)
          (hVI a) (hVI d))).symm
  have hvzero : eV.hom.hom.app Z (0 : (GV.obj (RF.obj X)).obj.obj Z) =
      (AddMonObj.zero (X := (RF.obj X).X)).hom.app Z PUnit.unit := by
    apply hinj
    exact (hVI 0).trans (hv.2.1 PUnit.unit).symm
  have hvone : eV.hom.hom.app Z (1 : (GV.obj (RF.obj X)).obj.obj Z) =
      (MonObj.one (X := (RF.obj X).X)).hom.app Z PUnit.unit := by
    apply hinj
    exact (hVI 1).trans (hv.2.2.2 PUnit.unit).symm
  have hradd (a d : (RF.obj X).X.obj.obj Z) :
      eR.hom.hom.app Z ((AddMonObj.add (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (AddMonObj.add (X := X.X)).hom.app (b.op.obj Z)
          (eR.hom.hom.app Z a, eR.hom.hom.app Z d) := by
    have hh := congrArg (fun g => g.hom.app Z (a, d)) (hOps X).1
    change eR.hom.hom.app Z
      ((AddMonObj.add (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (AddMonObj.add (X := X.X)).hom.app (b.op.obj Z)
          ((prodComparisonIso R X.X X.X).inv.hom.app Z
            (eR.hom.hom.app Z a, eR.hom.hom.app Z d)) at hh
    rw [hprod] at hh
    exact hh
  have hrmul (a d : (RF.obj X).X.obj.obj Z) :
      eR.hom.hom.app Z ((MonObj.mul (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (MonObj.mul (X := X.X)).hom.app (b.op.obj Z)
          (eR.hom.hom.app Z a, eR.hom.hom.app Z d) := by
    have hh := congrArg (fun g => g.hom.app Z (a, d)) (hOps X).2.2.2.1
    change eR.hom.hom.app Z
      ((MonObj.mul (X := (RF.obj X).X)).hom.app Z (a, d)) =
        (MonObj.mul (X := X.X)).hom.app (b.op.obj Z)
          ((prodComparisonIso R X.X X.X).inv.hom.app Z
            (eR.hom.hom.app Z a, eR.hom.hom.app Z d)) at hh
    rw [hprod] at hh
    exact hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a d
    change eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z (a + d))) =
      (show (GU.obj X).obj.obj (b.op.obj Z) from
        eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z a))) +
        (show (GU.obj X).obj.obj (b.op.obj Z) from
          eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z d)))
    rw [hvadd, hradd]
    exact hu'.1 _ _
  · change eU.inv.hom.app (b.op.obj Z)
      (eR.hom.hom.app Z (eV.hom.hom.app Z (0 : (GV.obj (RF.obj X)).obj.obj Z))) =
        (0 : (GU.obj X).obj.obj (b.op.obj Z))
    rw [hvzero]
    have hh := congrArg (fun g => g.hom.app Z PUnit.unit) (hOps X).2.1
    change eR.hom.hom.app Z
      ((AddMonObj.zero (X := (RF.obj X).X)).hom.app Z PUnit.unit) =
        (AddMonObj.zero (X := X.X)).hom.app (b.op.obj Z)
          ((preservesTerminalIso R).inv.hom.app Z PUnit.unit) at hh
    rw [hh]
    exact hu'.2.1 _
  · intro a d
    change eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z (a * d))) =
      (show (GU.obj X).obj.obj (b.op.obj Z) from
        eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z a))) *
        (show (GU.obj X).obj.obj (b.op.obj Z) from
          eU.inv.hom.app (b.op.obj Z) (eR.hom.hom.app Z (eV.hom.hom.app Z d)))
    rw [hvmul, hrmul]
    exact hu'.2.2.1 _ _
  · change eU.inv.hom.app (b.op.obj Z)
      (eR.hom.hom.app Z (eV.hom.hom.app Z (1 : (GV.obj (RF.obj X)).obj.obj Z))) =
        (1 : (GU.obj X).obj.obj (b.op.obj Z))
    rw [hvone]
    have hh := congrArg (fun g => g.hom.app Z PUnit.unit) (hOps X).2.2.2.2
    change eR.hom.hom.app Z
      ((MonObj.one (X := (RF.obj X).X)).hom.app Z PUnit.unit) =
        (MonObj.one (X := X.X)).hom.app (b.op.obj Z)
          ((preservesTerminalIso R).inv.hom.app Z PUnit.unit) at hh
    rw [hh]
    exact hu'.2.2.2 _

end AlgebraicGeometry
