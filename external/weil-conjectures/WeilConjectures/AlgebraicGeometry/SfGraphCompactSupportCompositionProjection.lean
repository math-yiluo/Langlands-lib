/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionForward

/-! # Projection compatibility of the fixed graph compositor

Source: blueprint proposition-composition-base-change-rf-shriek--1, composition pentagon.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local irreducible] projectionMapOfCompactification
  sfGraphCompactSupportCompIso Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

open Lean Elab Tactic Meta

private theorem graphProjectionProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private theorem graphTensor_obj_obj
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    (X : Scheme.{u}) [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B X).obj M).obj N = M ⊗ N := by
  unfold derivedTensor
  rfl

-- Reduce the three tensor APIs without unfolding their derived monoidal instance.
private meta def graphProjectionReduce (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``Functor.obj then
    let F := args[args.size - 2]!
    let N := args.back!
    if !F.getAppFn.isConstOf ``Functor.obj then return e
    let fs := F.getAppArgs
    let T := fs[fs.size - 2]!
    let M := fs.back!
    if T.getAppFn.isConstOf ``derivedTensor then
      let h ← mkAppOptM ``graphTensor_obj_obj
        ((T.getAppArgs.map some) ++ #[some M, some N])
      return (← inferType h).appArg!
    if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek ||
        T.getAppFn.isConstOf ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
      let thm := if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek then
        ``derivedTensorRightDerivedLowerShriek_obj_obj else
        ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
      let h := mkAppN (mkConst thm T.getAppFn.constLevels!) (T.getAppArgs ++ #[M, N])
      return (← inferType h).appArg!
  if e.getAppFn.isConstOf ``NatTrans.app then
    let a := args[args.size - 2]!
    let N := args.back!
    if !a.getAppFn.isConstOf ``Functor.map then return e
    let mapArgs := a.getAppArgs
    let T := mapArgs[mapArgs.size - 4]!
    let f := mapArgs.back!
    if T.getAppFn.isConstOf ``derivedTensor then
      let h ← mkAppOptM ``derivedTensor_map_app
        ((T.getAppArgs.map some) ++ #[none, none, some f, some N])
      return (← inferType h).appArg!
  if e.getAppFn.isConstOf ``Functor.map then
    let F := args[args.size - 4]!
    let f := args.back!
    if !F.getAppFn.isConstOf ``Functor.obj then return e
    let fs := F.getAppArgs
    let T := fs[fs.size - 2]!
    let M := fs.back!
    if T.getAppFn.isConstOf ``derivedTensor then
      let h ← mkAppOptM ``derivedTensor_obj_map
        ((T.getAppArgs.map some) ++ #[some M, none, none, some f])
      return (← inferType h).appArg!
  return e

-- Congruence and proof irrelevance produce ordinary kernel-checked proof terms.
private meta partial def graphProjectionCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  let an ← graphProjectionReduce a
  let bn ← graphProjectionReduce b
  if an != a || bn != b then return ← graphProjectionCongrHEq an bn
  if ← isProp (← inferType a) then
    let hp ← graphProjectionCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``graphProjectionProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← graphProjectionCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different projection expressions: {a} versus {b}; \
      heads {a.getAppFn} versus {b.getAppFn}; \
      right arguments {(b.getAppArgs.map fun x ↦ x.getAppFn)}"
  return ← mkHEqRefl a

/-- The explicitly constructed graph compositor preserves the projection maps.

Source: blueprint proposition-composition-base-change-rf-shriek--1, composition pentagon; steps 1--3
of lem-route-exists-right-derived-lower-shriek-comp-iso.
(auxiliary; not a blueprint node).

Proof: apply sfEtaleCompactProjectionInverse_composition to the three chosen
compactifications. All three projection components are invertible by
sfEtaleAmbientAdjointProjection. Precompose its equation with the projection
for the composite, then postcompose with the projection for g and the image
under g of the projection for f. Cancel the three inverse pairs. The resulting
forward equation is exactly ProjectionCompCompatible. Identify derivedTensor's
object and morphism APIs with tensor objects and whiskering, and unfold only
projectionMap and rightDerivedLowerShriek to identify the chosen compactifications.
The two coefficient braiding instances are definitionally equal; the conversion
must retain the derived-category constructions folded. This assertion involves
only projection maps, and imposes no base-change compatibility. -/
theorem sfGraphCompactSupportCompIso_projection
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Adjunction.ProjectionCompCompatible
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) (f ≫ g)).app M).app N)
      (fun N ↦ (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app N)
      (sfGraphCompactSupportCompIso Λ f g
        (HasCompactification.compactification f) (HasCompactification.compactification g)
        (HasCompactification.compactification (f ≫ g))) := by
  -- The existing forward square avoids cancelling the inverse projections.
  refine ⟨fun M N ↦ ?_⟩
  have h := sfEtaleCompactProjectionForward_composition Λ f g
    (HasCompactification.compactification f) (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g)) M N
  dsimp only [sfCompactProjection, Functor.comp_obj, Functor.comp_map] at h
  dsimp only [projectionMap, rightDerivedLowerShriek, Functor.comp_obj, Functor.comp_map]
  run_tac withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let decls := (← getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "no forward projection square"
    let eq ← graphProjectionCongrHEq target (← instantiateMVars d.type)
    let eq ← mkAppM ``eq_of_heq #[eq]
    let pf ← mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← getMainGoal).assign pf

end AlgebraicGeometry.Etale
