/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryRestrictionUnderlying
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps

/-! Target endpoint transport for the finite Chern coordinate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures
attribute [local implicit_reducible] spCoefficientCommRings
  SpTowerShriek.tau Functor.ofOpSequence Functor.ofSequence
  SemilinearSections.evaluation
attribute [local irreducible] SemilinearSections.scalarExtensionSection
  cartierProRootMap

private theorem finiteBoundaryTargetRestriction_inv_app
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ) :
    ((finiteBoundaryRestrictionUnderlying l T r n).inv.app M).hom.app U =
      eqToHom (r.underlying M n U).symm := by
  rfl

/-- Target endpoint transport.  The finite root map, the inverse line
comparison, the inverse restriction comparison and the coefficient lineForget
map, followed by the Cartier root map, equal the Cartier root map.  The proof
expands `finiteBoundary_rootMap`, uses the ordinary scalar unit and
`line_tensor`, and cancels the evaluation and restriction isomorphisms.
(blueprint: lem-diagonal-local-finite-target-endpoint-transport) -/
theorem finiteBoundary_target_endpoint
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (A : Type (u + 1))
    [CommRing A] (n : ℕ) (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
    let e := finiteBoundaryRestrictionUnderlying l T r n
    S.map (finiteRootMap l (ULift.{u} (Padic l)) T n) ≫
        S.map ((finiteForget l (ULift.{u} (Padic l)) T n).mapIso
          (lineEvaluation l (ULift.{u} (Padic l)) c n)).inv ≫
        S.map (e.inv.app (lineModule l (ULift.{u} (Padic l)) c)) ≫
        S.map (k.lineForget.hom.app (op n)) ≫
        S.map (cartierProRootMap A (l ^ (n + 1)) hA T
          (pow_pos (Fact.out : l.Prime).pos _) hN) =
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN) := by
  intro S e
  simp only [Functor.mapIso_inv, ← Functor.map_comp]
  apply congrArg S.map
  rw [← finiteBoundary_rootMap l (ULift.{u} (Padic l)) c n]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
  dsimp only [abEvaluation, Functor.comp_map, evaluation_obj_map]
  apply Sheaf.hom_ext
  ext U z
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply]
  dsimp only [e]
  rw [finiteBoundaryTargetRestriction_inv_app l T r n
    (lineModule l (ULift.{u} (Padic l)) c) U]
  let x' := (c.rootForget.inv.app (op n)).hom.app U z
  let x : c.rootModule.val.obj (op (n, U.unop)) :=
    (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
  have hx : HEq x' x := (finiteBoundary_cast_heq
    (c.reduction.forget.sections c.rootModule n U) x').symm
  let η := c.scalar.ordinaryAdjunction.unit.app c.rootModule
  have hf := finiteBoundary_forgetMapSection T _ c.reduction.forget η n U x x' hx
  have he := finiteScalarForgetIso_section l (ULift.{u} (Padic l)) c n
    (lineModule l (ULift.{u} (Padic l)) c) U _ _ hf
  have hu : η.val.app (op (n, U.unop)) x =
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)
        c.scalar c.rootModule (op (n, U.unop)) x :=
    scalarUnitSection.{u + 1, u, u + 1} _ c.scalar c.rootModule _ x
  let v : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj
      (lineModule l (ULift.{u} (Padic l)) c)).val.obj U :=
    ((finiteScalarForgetIso l (ULift.{u} (Padic l)) c n).hom.app
      (lineModule l (ULift.{u} (Padic l)) c)).hom.app U
        (((c.reduction.forget.F.map η).app (op n)).hom.app U x')
  let w := (eqToHom (r.underlying (lineModule l (ULift.{u} (Padic l)) c) n U).symm) v
  have hw : HEq w v := finiteBoundary_cast_heq
    (r.underlying (lineModule l (ULift.{u} (Padic l)) c) n U).symm v
  dsimp only [v] at hw
  have ht := k.line_tensor n U x x' w hx.symm
    (hw.trans ((heq_of_eq he).trans (heq_of_eq hu)))
  have hi := congrArg (fun f ↦ f.hom.app U z) (c.rootForget.app (op n)).inv_hom_id
  change (c.rootForget.hom.app (op n)).hom.app U x' = z at hi
  dsimp only [w, v, η, x'] at ht hi
  exact congrArg ((cartierProRootMap A (l ^ (n + 1)) hA T
    (pow_pos (Fact.out : l.Prime).pos _) hN).hom.app U) (ht.trans hi)

end AlgebraicGeometry.ProEtale.DiagonalTrace
