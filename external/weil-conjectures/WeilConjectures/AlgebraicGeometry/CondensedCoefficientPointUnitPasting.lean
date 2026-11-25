/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation

/-! # Point-unit pasting at terminal evaluation

Source: RefactorInstruction, Sections 4 and 5, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCoefficientUnit

-- Keep the adjunction calculation abstract before specializing to coefficient sheaves.
private theorem point_unit_mate {W X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :
    (upperStarLowerStarAdjunction Ab.{u + 1} kY).unit.app F ≫
        (lowerStar Ab.{u + 1} kY).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
              ((upperStar Ab.{u + 1} kY).obj F) ≫
            (lowerStar Ab.{u + 1} f).map
              ((upperStarComp Ab.{u + 1} f kY).inv.app F ≫
                (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app F)) =
      (upperStarLowerStarAdjunction Ab.{u + 1} kX).unit.app F ≫
        (lowerStarFactor Ab.{u + 1} hf).inv.app
          ((upperStar Ab.{u + 1} kX).obj F) := by
  subst kX
  simpa only [eqToHom_refl, NatTrans.id_app, Category.comp_id,
    lowerStarFactor, lowerStarComp] using
    unit_comp_lowerStar_map_unit_comp_upperStarComp' Ab.{u + 1} f kY F

private theorem point_unit_mate_condensed {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).unit.app (pointUpperStar.obj Λ) ≫
        (lowerStar Ab.{u + 1} (toSpecZ Y)).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app (condensedRingObj Λ Y) ≫
            (lowerStar Ab.{u + 1} f).map (condensedPullbackHom Λ f)) =
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).unit.app (pointUpperStar.obj Λ) ≫
        (lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).inv.app (condensedRingObj Λ X) := by
  have h := point_unit_mate f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) (pointUpperStar.obj Λ)
  rw [← condensedPullbackHom_eq] at h
  exact h

private theorem test_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (Functor.sheafPushforwardContinuousComp'
      (eFG := geometricFieldTestBaseChange f) Ab.{u + 1}
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).hom.app G =
    pointLowerStar.map ((lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).hom.app G) := by
  ext S
  simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    pointLowerStar, Functor.sheafPushforwardContinuous_map_hom_app,
    lowerStarFactor_hom_app_hom_app]
  congr 1

private theorem mate_cancel {W X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (A : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (G B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (uY : F ⟶ (lowerStar Ab.{u + 1} kY).obj A)
    (uX : F ⟶ (lowerStar Ab.{u + 1} kX).obj B)
    (η : A ⟶ (lowerStar Ab.{u + 1} f).obj G) (α : G ⟶ B)
    (h : uY ≫ (lowerStar Ab.{u + 1} kY).map
        (η ≫ (lowerStar Ab.{u + 1} f).map α) =
      uX ≫ (lowerStarFactor Ab.{u + 1} hf).inv.app B) :
    uY ≫ (lowerStar Ab.{u + 1} kY).map η ≫
        (lowerStarFactor Ab.{u + 1} hf).hom.app G ≫
        (lowerStar Ab.{u + 1} kX).map α = uX := by
  rw [← (lowerStarFactor Ab.{u + 1} hf).hom.naturality α]
  calc
    _ = (uY ≫ (lowerStar Ab.{u + 1} kY).map
        (η ≫ (lowerStar Ab.{u + 1} f).map α)) ≫
        (lowerStarFactor Ab.{u + 1} hf).hom.app B := by
      simp only [CategoryTheory.Functor.map_comp, Functor.comp_map, Category.assoc]
    _ = uX := by rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

-- These equations expose restriction maps without unfolding the inverse-image sheaves.
private theorem restriction_map (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (α : F ⟶ G) :
    (geometricFieldRestriction X Ab).map α =
      pointLowerStar.map ((lowerStar Ab.{u + 1} (toSpecZ X)).map α) := by
  rfl

private theorem abelian_scheme_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    (Scheme.proEtaleSheafAdjunction f Ab).unit.app A =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A := by
  rfl

private theorem point_unit_sheaf_component (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (geometricFieldAbelianPointAdjunction X).unit.app Λ =
      pointUpperStarLowerStarAdjunction.unit.app Λ ≫ pointLowerStar.map
        ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).unit.app
          (pointUpperStar.obj Λ)) := by
  rfl

private theorem point_unit_restriction_sheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (geometricFieldAbelianPointAdjunction Y).unit.app Λ ≫
        (geometricFieldRestrictionComparison f Ab).app (condensedRingObj Λ Y) ≫
        (geometricFieldRestriction X Ab).map (condensedPullbackHom Λ f) =
      (geometricFieldAbelianPointAdjunction X).unit.app Λ := by
  let F := pointUpperStar.obj Λ
  let A := condensedRingObj Λ Y
  let B := condensedRingObj Λ X
  let G := (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).obj A
  let α : G ⟶ B := condensedPullbackHom Λ f
  let uY := (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).unit.app F
  let uX := (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).unit.app F
  let η := (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A
  have h := mate_cancel f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    F A G B uY uX η α (point_unit_mate_condensed f Λ)
  have hp := congrArg (fun k ↦
    pointUpperStarLowerStarAdjunction.unit.app Λ ≫ pointLowerStar.map k) h
  simp only [CategoryTheory.Functor.map_comp] at hp
  rw [point_unit_sheaf_component, point_unit_sheaf_component]
  simp only [geometricFieldRestrictionComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [test_pushforward]
  rw [restriction_map, restriction_map, abelian_scheme_unit]
  simp only [Category.assoc] at hp ⊢
  exact hp

private theorem restriction_map_component (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (α : F ⟶ G)
    (S : Profinite.{u}) :
    ((geometricFieldRestriction X Ab).map α).hom.app (op S) =
      α.hom.app (op ((profiniteToProEtOf X).obj S)) := by
  rfl

private theorem point_unit_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (S : Profinite.{u}) :
    ((geometricFieldAbelianPointAdjunction Y).unit.app Λ).hom.app (op S) ≫
        ((geometricFieldRestrictionComparison f Ab).app (condensedRingObj Λ Y)).hom.app
          (op S) ≫
        (condensedPullbackHom Λ f).hom.app (op ((profiniteToProEtOf X).obj S)) =
      ((geometricFieldAbelianPointAdjunction X).unit.app Λ).hom.app (op S) := by
  have h := congrArg (fun k ↦ k.hom.app (op S)) (point_unit_restriction_sheaf f Λ)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restriction_map_component] using h

private theorem section_pasting
    {L AY AV GT GW BT BW : Ab.{u + 1}}
    (uY : L ⟶ AV) (uX : L ⟶ BW) (qY : AY ⟶ AV) (r : AV ⟶ GW)
    (e : AY ⟶ GT) (qG : GT ⟶ GW) (qB : BT ⟶ BW) [IsIso qB]
    (αT : GT ⟶ BT) (αW : GW ⟶ BW)
    (hc : qY ≫ r = e ≫ qG) (hu : uY ≫ r ≫ αW = uX)
    (hn : qG ≫ αW = αT ≫ qB)
    (a : L) (y : AY) (y' : BT)
    (hy : uY.hom a = qY.hom y) (hy' : uX.hom a = qB.hom y') :
    αT.hom (e.hom y) = y' := by
  apply (ConcreteCategory.bijective_of_isIso qB).1
  have hc' := congrArg (fun k ↦ k.hom y) hc
  have hu' := congrArg (fun k ↦ k.hom a) hu
  have hn' := congrArg (fun k ↦ k.hom (e.hom y)) hn
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hc' hu' hn'
  change qB.hom (αT.hom (e.hom y)) = qB.hom y'
  rw [← hn', ← hc', ← hy]
  exact hu'.trans hy'

private theorem inverse_section {X : Scheme.{u}}
    {G B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    (α : G ⟶ B) [IsIso α] (T : X.ProEt)
    (z : G.obj.obj (op T)) (y' : B.obj.obj (op T))
    (h : (α.hom.app (op T)).hom z = y') :
    z = ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation _ _).obj (op T)).map (inv α)).hom y' := by
  let E := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (evaluation _ _).obj (op T)
  have hinv := congrArg (fun w ↦ (E.map (inv α)).hom w) h
  have hid : α.hom.app (op T) ≫ E.map (inv α) = 𝟙 _ := by
    change E.map α ≫ E.map (inv α) = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have hid' := congrArg (fun k ↦ k.hom z) hid
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
    AddCommGrpCat.hom_id] at hid'
  exact hid'.symm.trans hinv

-- Do the section calculation for arbitrary sheaves; specialize only in terminal_transport.
private theorem transport_of_unit (K K' : Type u) [Field K] [IsAlgClosed K]
    [Field K'] [IsAlgClosed K'] (i : K →+* K')
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1})
    (α : (upperStar Ab.{u + 1} (Spec.map (CommRingCat.ofHom i))).obj A ⟶ B)
    [IsIso α] (L : Ab.{u + 1})
    (uY : L ⟶ A.obj.obj (op ((profiniteToProEtOf (Spec (.of K))).obj
      (Profinite.of (ULift.{u, 0} PUnit.{1})))))
    (uX : L ⟶ B.obj.obj (op ((profiniteToProEtOf (Spec (.of K'))).obj
      (Profinite.of (ULift.{u, 0} PUnit.{1})))))
    (hu : uY ≫ ((geometricFieldRestrictionComparison
        (Spec.map (CommRingCat.ofHom i)) Ab).app A).hom.app
          (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) ≫
      α.hom.app (op ((profiniteToProEtOf (Spec (.of K'))).obj
        (Profinite.of (ULift.{u, 0} PUnit.{1})))) = uX)
    (a : L) (y : A.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))
    (y' : B.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K'))))))
    (hy : uY.hom a = (A.obj.map (geometricFieldTestFinalMap (Spec (.of K))).op).hom y)
    (hy' : uX.hom a = (B.obj.map (geometricFieldTestFinalMap (Spec (.of K'))).op).hom y') :
    ((geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) Ab).app A).hom y =
      ((sheafToPresheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))).map
          (inv α)).hom y' := by
  let X := Spec (.of K')
  let Y := Spec (.of K)
  let f := Spec.map (CommRingCat.ofHom i)
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  let V := (profiniteToProEtOf Y).obj S
  let W := (profiniteToProEtOf X).obj S
  let T := Scheme.ProEt.mk (𝟙 X)
  let G := (upperStar Ab.{u + 1} f).obj A
  let qX : W ⟶ T := geometricFieldTestFinalMap X
  let qY := geometricFieldTestFinalMap Y
  let e : A.obj.obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶ G.obj.obj (op T) :=
    (geometricFieldEvaluationComparison f Ab).app A
  let r : A.obj.obj (op V) ⟶ G.obj.obj (op W) :=
    ((geometricFieldRestrictionComparison f Ab).app A).hom.app (op S)
  have : IsIso qX := (geometric_field_proetale_evaluation K').2.2.2.2.2.2.2.1
  have hcoh : A.obj.map qY.op ≫ r = e ≫ G.obj.map qX.op :=
    (geometric_field_proetale_evaluation_coherence K K' K' i (RingHom.id K') Ab).1 A
  have hforward : (α.hom.app (op T)).hom (e.hom y) = y' :=
    section_pasting uY uX (A.obj.map qY.op) r e (G.obj.map qX.op)
      (B.obj.map qX.op) (α.hom.app (op T)) (α.hom.app (op W))
      hcoh hu (α.hom.naturality qX.op) a y y' hy hy'
  exact inverse_section α T (e.hom y) y' hforward

/-- Terminal evaluation transports every section represented by the point unit.

Source: RefactorInstruction, Section 4, lem:XS and prop:pX, and Section 5,
eq:triangle; Bhatt--Scholze, Example 4.1.10.
(auxiliary; not a blueprint node).

Proof in words: write X = Spec K', Y = Spec K, f = Spec i, and S for the
singleton profinite set. Let qY and qX be the specified structural maps from
Y[S] and X[S] to the final objects. Put A = condensedRingObj Λ Y,
B = condensedRingObj Λ X, and alpha = condensedPullbackHom Λ f.
The evaluation-coherence equation, evaluated on y, identifies restriction of
geometricFieldEvaluationComparison(f)(y) along qX with restrictionComparison(f)
applied to restriction of y along qY. Naturality of alpha along qX moves alpha
from the terminal object to X[S]. The hypothesis identifies the latter restricted
section of A with the point-adjunction unit applied to a.

It remains to identify the point unit followed by restrictionComparison(f) and
alpha on X[S] with the point unit over X. Expand restrictionComparison(f) as the
f-adjunction unit followed by restriction along geometricFieldTestBaseChange(f)
inverse. Naturality of alpha along that inverse moves alpha before restriction.
Expand alpha by condensedPullbackHom_eq. Apply the source-library identity
unit_comp_lowerStar_map_unit_comp_upperStarComp' to f and toSpecZ Y, evaluate it
at profiniteToProEt.obj S, and precompose with the point adjunction unit at a.
Postcompose with restriction along pullbackComp forward; its inverse cancels.
Transport the composite structural map using comp_toSpecZ f. The resulting
composite unit is exactly geometricFieldAbelianPointAdjunction X. This proves
the required equality, with every comparison the specified one.

The argument uses no scalar coordinates and no finiteness or algebraicity
assumption on i. Zero sections and identity embeddings satisfy the same unit and
naturality identities. Finally the singleton structural map qX is invertible over the
algebraically closed
field Kprime by geometric_field_proetale_evaluation. Its presheaf restriction has
inverse given by restriction along qX inverse. Cancel this restriction, using hyprime,
to identify the forward terminal section with yprime. Finally apply the evaluated
inverse of alpha, using Functor.map_comp and the inverse identity of alpha, to obtain
the displayed inverse-comparison equation. -/
theorem terminal_transport (K K' : Type u) [Field K] [IsAlgClosed K]
    [Field K'] [IsAlgClosed K'] (i : K →+* K')
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (a : Λ.obj.obj (op (Profinite.of (ULift.{u, 0} PUnit.{1}))))
    (y : (condensedRingObj Λ (Spec (.of K))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))
    (hy : (((geometricFieldAbelianPointAdjunction (Spec (.of K))).unit.app Λ).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1})))).hom a =
      ((condensedRingObj Λ (Spec (.of K))).obj.map
        (geometricFieldTestFinalMap (Spec (.of K))).op).hom y)
    (y' : (condensedRingObj Λ (Spec (.of K'))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K'))))))
    (hy' : (((geometricFieldAbelianPointAdjunction (Spec (.of K'))).unit.app Λ).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1})))).hom a =
      ((condensedRingObj Λ (Spec (.of K'))).obj.map
        (geometricFieldTestFinalMap (Spec (.of K'))).op).hom y') :
    let f := Spec.map (CommRingCat.ofHom i)
    let E' := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of K'))) Ab.{u + 1} ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))
    ((geometricFieldEvaluationComparison f Ab).app
      (condensedRingObj Λ (Spec (.of K)))).hom y =
    (E'.map (inv (condensedPullbackHom Λ f))).hom y' := by
  exact transport_of_unit K K' i (condensedRingObj Λ (Spec (.of K)))
    (condensedRingObj Λ (Spec (.of K'))) (condensedPullbackHom Λ (Spec.map (CommRingCat.ofHom i)))
    (Λ.obj.obj (op (Profinite.of (ULift.{u, 0} PUnit.{1}))))
    (((geometricFieldAbelianPointAdjunction (Spec (.of K))).unit.app Λ).hom.app
      (op (Profinite.of (ULift.{u, 0} PUnit.{1}))))
    (((geometricFieldAbelianPointAdjunction (Spec (.of K'))).unit.app Λ).hom.app
      (op (Profinite.of (ULift.{u, 0} PUnit.{1}))))
    (point_unit_restriction (Spec.map (CommRingCat.ofHom i)) Λ _) a y y' hy hy'

end AlgebraicGeometry.ProEtale.CondensedCoefficientUnit
