/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation

/-! # Normalization of geometric coefficient coordinates on the singleton

Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
private noncomputable def boundedConstant (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Type u) [TopologicalSpace T] (r : PadicAlgCl ℓ) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ T := by
  have hr : _root_.IsIntegral ℚ_[ℓ] r := Algebra.IsIntegral.isIntegral r
  exact ⟨ContinuousMap.const _ r,
    ⟨IntermediateField.adjoin ℚ_[ℓ] {r}, IntermediateField.adjoin.finiteDimensional hr,
      fun _ ↦ IntermediateField.subset_adjoin ℚ_[ℓ] _ (Set.mem_singleton r)⟩⟩

private theorem terminal_coefficient_value (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] (r : PadicAlgCl ℓ) :
    ((CondensedQbarCoefficientRealization.globalCoefficientIso ℓ (Spec (.of K))).hom.hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).hom
        ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom).hom
          (ULift.up r)) =
    ((CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).hom.hom).hom
      (ULift.up (boundedConstant ℓ (Spec (.of K)) r)) := by
  let e := (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ
    (Spec (.of K))).hom.hom.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
  let U := (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).hom.hom
  let b := (CondensedQbarGeometricEvaluation.boundedPointIso K ℓ).hom.hom
  let c := (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom
  let v := (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ).inv.hom
  have hc : c = (e ≫ v) ≫ b := by rfl
  have hb : b.hom (ULift.up (boundedConstant ℓ (Spec (.of K)) r)) = ULift.up r := by rfl
  have hi := congrArg (fun a ↦ a.hom (ULift.up r)) (IsIso.inv_hom_id c)
  change c.hom ((inv c).hom (ULift.up r)) = ULift.up r at hi
  have hi := (congrArg (fun k ↦ k.hom ((inv c).hom (ULift.up r))) hc).symm.trans hi
  change b.hom (v.hom (e.hom ((inv c).hom (ULift.up r)))) = ULift.up r at hi
  have hh := (ConcreteCategory.bijective_of_isIso b).1 (hi.trans hb.symm)
  have hu := congrArg (fun x ↦ U.hom x) hh
  change e.hom ((inv c).hom (ULift.up r)) = U.hom _
  have hvu : v ≫ U = 𝟙 _ := congrArg (fun k ↦ k.hom)
    (Iso.inv_hom_id (CondensedQbarGeometricEvaluation.fieldUnitIso K ℓ))
  have hx := congrArg (fun k ↦ k.hom (e.hom ((inv c).hom (ULift.up r)))) hvu
  change U.hom (v.hom _) = _ at hx
  exact hx.symm.trans hu
private theorem point_coefficient_value (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] (r : PadicAlgCl ℓ) :
    let X := Spec (.of K)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
    let q := geometricFieldTestFinalMap X
    let S := Profinite.of (ULift.{u, 0} PUnit.{1})
    (((geometricFieldAbelianPointAdjunction X).unit.app
      (Profinite.padicAlgClRingObj ℓ)).hom.app (op S)).hom
        (ULift.up (boundedConstant ℓ S r)) =
    (A.obj.map q.op).hom
      ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom).hom
        (ULift.up r)) := by
  dsimp only
  let X := Spec (.of K)
  let S := Profinite.of (ULift.{u, 0} PUnit.{1})
  let q := geometricFieldTestFinalMap X
  let e := CondensedQbarCoefficientRealization.globalCoefficientIso ℓ X
  let c := (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom
  let a := boundedConstant ℓ S r
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.hom.app
    (op ((profiniteToProEtOf X).obj S)))).1
  have ht := CondensedQbarCoefficientRealization.globalCoefficientIso_test ℓ X S a
  change (e.hom.hom.hom.app _).hom
    ((((geometricFieldAbelianPointAdjunction X).unit.app
      (Profinite.padicAlgClRingObj ℓ)).hom.app (op S)).hom (ULift.up a)) = _ at ht
  change (e.hom.hom.hom.app _).hom _ = (e.hom.hom.hom.app _).hom _
  erw [ht]
  have hn := congrArg (fun k ↦ k.hom ((inv c).hom (ULift.up r)))
    (e.hom.hom.hom.naturality q.op)
  change (e.hom.hom.hom.app _).hom
      (((condensedRingObj (Profinite.padicAlgClRingObj ℓ) X).obj.map q.op).hom _) =
    ((padicAlgClSheaf X ℓ).obj.map q.op).hom
      ((e.hom.hom.hom.app _).hom _) at hn
  erw [hn, terminal_coefficient_value]
  have hu := congrArg (fun k ↦ k.hom
    (ULift.up (boundedConstant ℓ X r)))
    ((toSheafify (Scheme.ProEt.topology X)
      (CondensedQbarScalarConstruction.boundedP ℓ X)).naturality q.op)
  change _ = _ at hu
  let t := toSheafify (Scheme.ProEt.topology X)
    (CondensedQbarScalarConstruction.boundedP ℓ X)
  change _ = ((padicAlgClSheaf X ℓ).obj.map q.op).hom
    ((t.app (op (Scheme.ProEt.mk (𝟙 X)))).hom (ULift.up (boundedConstant ℓ X r)))
  erw [← hu]
  congr 1
/-- The chosen coefficient coordinates agree with the point-adjunction unit on the
singleton profinite test object.

Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers
(auxiliary; not a blueprint node).

Proof: every bounded function on the singleton is constant. Choose its value r and
construct the constant bounded function on Spec(K), using the finite intermediate
field generated by r; integrality over Q_l makes this field finite. By the definition
of fieldCoefficientIso, its inverse sends r first through boundedPointIso inverse,
then through the terminal bounded-presheaf unit, and then through the inverse global
coefficient realization. Apply globalCoefficientIso_test to the singleton function.
Naturality of that realization and of the bounded-presheaf unit along the structural
map from the test scheme to Spec(K) identifies both resulting sections: pullback of a
constant bounded function is constant with the same value. Cancel the evaluated
realization, which is an isomorphism. This also covers r = 0 and every characteristic
of the algebraically closed field K. -/
theorem condensedQbar_field_point_coefficient_value (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type u) [Field K] [IsAlgClosed K]
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ
      (Profinite.of (ULift.{u, 0} PUnit.{1}))) :
    let X := Spec (.of K)
    let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
    let S := Profinite.of (ULift.{u, 0} PUnit.{1})
    (((geometricFieldAbelianPointAdjunction X).unit.app
      (Profinite.padicAlgClRingObj ℓ)).hom.app (op S)).hom (ULift.up a) =
    (A.obj.map (geometricFieldTestFinalMap X).op).hom
      ((inv (CondensedQbarGeometricEvaluation.fieldCoefficientIso K ℓ).hom.hom).hom
        (ULift.up (a.1 default))) := by
  dsimp only
  have h := point_coefficient_value ℓ K (a.1 default)
  have ha : boundedConstant ℓ (Profinite.of (ULift.{u, 0} PUnit.{1}))
      (a.1 default) = a := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg a.1 (Subsingleton.elim default x)
  simpa only [ha] using h
end AlgebraicGeometry.ProEtale
