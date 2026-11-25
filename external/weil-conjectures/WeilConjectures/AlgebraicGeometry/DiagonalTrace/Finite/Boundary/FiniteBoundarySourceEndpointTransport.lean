/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryRestrictionUnderlying
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints

/-! Source endpoint transport for the finite Chern coordinate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
attribute [local implicit_reducible] spCoefficientCommRings

private theorem finiteBoundarySourceRestriction_inv_section
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj M).val.obj U) :
    HEq (((finiteBoundaryRestrictionUnderlying l T r n).inv.app M).hom.app U x) x := by
  change HEq ((eqToHom (r.underlying M n U).symm) x) x
  exact finiteBoundary_cast_heq _ _

/-- Source endpoint transport.  This is the coefficient-one calculation: the
finite quotient followed by the restricted evaluation comparison is the
integer coefficient map.  The proof is the coefficient-one section calculation,
additivity, and the constant-sheaf adjunction.
(blueprint: lem-diagonal-local-finite-source-endpoint-transport) -/
theorem finiteBoundary_source_endpoint
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) :
    let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
    let e := finiteBoundaryRestrictionUnderlying l T r n
    S.map (finiteQuotient l (ULift.{u} (Padic l)) T n) ≫
        S.map (e.inv.app (coefficient T (Arings l (ULift.{u} (Padic l)) T))) =
      S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n)) := by
  intro S e
  rw [← S.map_comp]
  apply congrArg S.map
  rw [← Iso.app_inv k.coefficientForget, Iso.eq_comp_inv]
  apply constantAb_ext_one
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply]
  let U := op (Scheme.ProEt.mk (𝟙 T))
  let z := (toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U
      (ULift.up 1)
  let x' := (finiteQuotient l (ULift.{u} (Padic l)) T n).hom.app U z
  let x := (e.inv.app (coefficient T (Arings l (ULift.{u} (Padic l)) T))).hom.app U x'
  have hq := (finiteQuotient_existsUnique l (ULift.{u} (Padic l)) T n).exists.choose_spec
    U (ULift.up 1)
  have hx' : HEq x' (1 : (systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop))) := by
    simpa only [x', z, finiteQuotient, Int.cast_one] using hq
  have hx : HEq x x' := by
    dsimp only [x, e]
    exact finiteBoundarySourceRestriction_inv_section l T r n
      (coefficient T (Arings l (ULift.{u} (Padic l)) T)) U x'
  have ha := k.coefficient_one n U x (hx.trans hx')
  have hi := integerMap_sections T (Scheme.purTwistFiniteRing T l n) U 1
  rw [Int.cast_one] at hi
  dsimp only [x, x', z, U] at ha
  dsimp only [U] at hi
  exact ha.trans hi.symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
