/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import all WeilConjectures.AlgebraicGeometry.ShriekTensorComposition

/-! # Composition coherence of proper projection maps

(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

private theorem forward_inverse_square
    {D E : Type*} [Category D] [Category E] (T : D ⥤ E)
    {W X : D} {Y Z : E} (a : W ≅ X) (b : Y ≅ Z)
    (p : T.obj X ⟶ Z) (q : T.obj W ⟶ Y)
    (h : p ≫ b.inv = T.map a.inv ≫ q) :
    T.map a.hom ≫ p = q ≫ b.hom := by
  apply (cancel_mono b.inv).1
  simp only [Category.assoc]
  rw [h, ← T.map_comp_assoc, a.hom_inv_id]
  rw [T.map_id, _root_.CategoryTheory.Category.id_comp, b.hom_inv_id,
    _root_.CategoryTheory.Category.comp_id]

private theorem forward_projection_square
    {D E : Type*} [Category D] [Category E] (T : E ⥤ E ⥤ E)
    {F G : D ⥤ E} (c : F ≅ G) (e : G ≅ F) (he : e.hom = c.inv)
    (v n : D) (m : E)
    (p : (T.obj (G.obj v)).obj m ⟶ G.obj n)
    (q : (T.obj (F.obj v)).obj m ⟶ F.obj n)
    (h : p ≫ e.hom.app n = (T.map (e.hom.app v)).app m ≫ q) :
    (T.map (c.hom.app v)).app m ≫ p = q ≫ c.hom.app n := by
  rw [he] at h
  exact forward_inverse_square (T.flip.obj m) (c.app v) (c.app n) p q h

private theorem forward_projection_path
    {D E : Type*} [Category D] [Category E] (T : E ⥤ E ⥤ E)
    {F G : D ⥤ E} (c : F ≅ G) (e : G ≅ F) (he : e.hom = c.inv)
    (v n : D) (m : E) {P Q : E}
    (p₁ : (T.obj (G.obj v)).obj m ⟶ P) (p₂ : P ⟶ G.obj n)
    (q₁ : (T.obj (F.obj v)).obj m ⟶ Q) (q₂ : Q ⟶ F.obj n)
    (h : p₁ ≫ p₂ ≫ e.hom.app n = (T.map (e.hom.app v)).app m ≫ q₁ ≫ q₂) :
    (T.map (c.hom.app v)).app m ≫ p₁ ≫ p₂ = q₁ ≫ q₂ ≫ c.hom.app n := by
  have hs := forward_projection_square T c e he v n m (p₁ ≫ p₂) (q₁ ≫ q₂)
    (by simpa only [Category.assoc] using h)
  simpa only [Category.assoc] using hs

private theorem projection_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.HasCompactification f]
    (V : DerivedCategoryModule A X) :
    (projectionIso A f V).hom = (projectionMap (ModuleCat.{u + 1} A) f).app V := by
  rw [projectionIso, asIso_hom]

private theorem trace_pull_eq (A : Type (u + 1)) [CommRing A]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    CoordinateTrace.pull A f = (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor := rfl

private theorem trace_push_eq (A : Type (u + 1)) [CommRing A]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.HasCompactification f] :
    SupportedTrace.push A f = rightDerivedLowerShriek (ModuleCat.{u + 1} A) f := rfl

open Lean Elab Tactic Meta in
private theorem projection_proof_heq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private theorem projection_source_functor
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y}
    (c : AlgebraicGeometry.Compactification f)
    (V : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (derivedTensorRightDerivedLowerShriek B c).obj V =
      (derivedTensor B Y).obj ((rightDerivedLowerShriekOfCompactification B c).obj V) := rfl

private theorem projection_target_functor
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y}
    (c : AlgebraicGeometry.Compactification f)
    (V : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar B c).obj V =
      (upperStar B f).leftDerivedFunctor ⋙ (derivedTensor B X).obj V ⋙
        rightDerivedLowerShriekOfCompactification B c := rfl

-- Normalize only functor wrappers, retaining their proved equations. Unfolding the
-- derived constructions themselves makes concrete coefficient instances expensive to compare.
open Lean Elab Tactic Meta in
private meta def projectionReduction (e : Expr) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``Iso.hom then
    let c := args.back!
    if c.getAppFn.isConstOf ``projectionIso then
      return some (← mkAppOptM ``projection_hom (c.getAppArgs.map some))
  if e.getAppFn.isConstOf ``CoordinateTrace.pull then
    return some (← mkAppOptM ``trace_pull_eq (args.map some))
  if e.getAppFn.isConstOf ``SupportedTrace.push then
    return some (← mkAppOptM ``trace_push_eq (args.map some))
  if e.getAppFn.isConstOf ``rightDerivedLowerShriek then
    return some (← mkAppOptM ``rightDerivedLowerShriek_eq (args.map some))
  let mut head := e
  let mut objs := #[]
  while head.getAppFn.isConstOf ``Functor.obj do
    let hs := head.getAppArgs
    objs := objs.push hs.back!
    head := hs[hs.size - 2]!
  if head.getAppFn.isConstOf ``Functor.whiskeringLeft₂ && objs.size == 5 then
    return some (← mkAppOptM ``Functor.whiskeringLeft₂_obj_obj_obj_obj_obj
      ((head.getAppArgs.map some) ++ (objs.reverse.map some)))
  if head.getAppFn.isConstOf ``Functor.postcompose₂ && objs.size == 4 then
    return some (← mkAppOptM ``Functor.postcompose₂_obj_obj_obj_obj
      ((head.getAppArgs.map some) ++ (objs.reverse.map some)))
  if e.getAppFn.isConstOf ``CategoryTheory.Functor.map then
    let F := args[args.size - 4]!
    if F.getAppFn.isConstOf ``Functor.comp then
      let fs := F.getAppArgs
      return some (← mkAppM ``CategoryTheory.Functor.comp_map
        #[fs[fs.size - 2]!, fs.back!, args.back!])
  if !e.getAppFn.isConstOf ``Functor.obj then return none
  let F := args[args.size - 2]!
  let N := args.back!
  if F.getAppFn.isConstOf ``Functor.id then
    return some (← mkAppOptM ``Functor.id_obj ((F.getAppArgs.map some) ++ #[some N]))
  if F.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek ||
      F.getAppFn.isConstOf ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
    let thm := if F.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek then
      ``projection_source_functor else ``projection_target_functor
    return some (← mkAppOptM thm ((F.getAppArgs.map some) ++ #[some N]))
  if F.getAppFn.isConstOf ``Functor.comp then
    return some (← mkAppOptM ``Functor.comp_obj ((F.getAppArgs.map some) ++ #[some N]))
  if !F.getAppFn.isConstOf ``Functor.obj then return none
  let fs := F.getAppArgs
  let T := fs[fs.size - 2]!
  let M := fs.back!
  if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek ||
      T.getAppFn.isConstOf ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
    let thm := if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek then
      ``derivedTensorRightDerivedLowerShriek_obj_obj else
      ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    return some (← mkAppOptM thm ((T.getAppArgs.map some) ++ #[some M, some N]))
  return none

-- Congruence and proof irrelevance compare the two local tensor-instance conventions.
-- Cache repeated comparisons and let the kernel check each small auxiliary proof separately.
open Lean Elab Tactic Meta in
mutual
private meta partial def projectionCongr (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if let some h := (← get).get? (a, b) then return h
  let h ← projectionCongrStep a b
  modify (·.insert (a, b) h)
  return h

private meta partial def projectionCongrStep (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some h ← projectionReduction a then
    let an := (← inferType h).appArg!
    let hn ← projectionCongr an b
    let ha ← mkAppM ``heq_of_eq #[h]
    let pf ← mkAppM ``HEq.trans #[ha, hn]
    return ← mkAuxTheorem (← inferType pf) pf (zetaDelta := true) (kind? := `_projection)
  if let some h ← projectionReduction b then
    let bn := (← inferType h).appArg!
    let hn ← projectionCongr a bn
    let hb ← mkAppM ``heq_of_eq #[h]
    let hb ← mkAppM ``HEq.symm #[hb]
    let pf ← mkAppM ``HEq.trans #[hn, hb]
    return ← mkAuxTheorem (← inferType pf) pf (zetaDelta := true) (kind? := `_projection)
  if ← isProp (← inferType a) then
    let hp ← projectionCongr (← inferType a) (← inferType b)
    let eq ← mkAppM ``eq_of_heq #[hp]
    let pf ← mkAppM ``projection_proof_heq #[a, b, eq]
    return ← mkAuxTheorem (← inferType pf) pf (zetaDelta := true) (kind? := `_projection)
  let af := a.getAppFn.consumeMData
  let bf := b.getAppFn.consumeMData
  if af == bf && a.getAppArgs.size == b.getAppArgs.size then
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    let ct ← mkHCongrWithArity af aa.size
    let mut ps := #[]
    for i in [:aa.size] do
      let mut h ← try projectionCongr aa[i]! bb[i]! catch err =>
        if a.getAppFn.isConstOf ``CategoryTheory.Functor.map then
          throwError "In map argument {i}: {aa[i]!} versus {bb[i]!}: {err.toMessageData}"
        throwError "In {a.getAppFn}, argument {i}: {err.toMessageData}"
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[aa[i]!, bb[i]!, h]
    let pf := mkAppN ct.proof ps
    let pf ← if (← inferType pf).isHEq then pure pf else mkAppM ``heq_of_eq #[pf]
    return ← mkAuxTheorem (← inferType pf) pf (zetaDelta := true) (kind? := `_projection)
  unless ← withTransparency .default (isDefEq a b) do
    throwError "Different projection expressions: {a} and {b}; \
      heads {a.getAppFn} / {b.getAppFn}; arities {a.getAppArgs.size} / {b.getAppArgs.size}"
  return ← mkHEqRefl a

end

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]

section SourceConvention

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
private local instance essentiallySmall_etale_tensorConvention (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedTensorSymmetry derivedTensor
  unboundedEtaleLowerShriekCompIso projectionMapOfCompactification
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  rightDerivedLowerShriekCompIso rightDerivedLowerShriekCongrIso projectionMap
attribute [local implicit_reducible] rightDerivedLowerShriek

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem composition_forward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] :
    (unboundedEtaleLowerShriekCompIso A f g).inv =
      (rightDerivedLowerShriekCongrIso A (rfl : f ≫ g = f ≫ g) ≪≫
        rightDerivedLowerShriekCompIso A f g).hom := by
  simp only [rightDerivedLowerShriekCongrIso, Iso.refl_trans]
  ext K
  simp only [unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, rightDerivedLowerShriek, Category.assoc]

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem projection_square_forward {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g]
    (V : DerivedCategoryModule A X) (M : DerivedCategoryModule A Z) :
    let k := (unboundedEtaleLowerShriekCompIso A f g).symm
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map (k.hom.app V)).app M ≫
      ((projectionMap (ModuleCat.{u + 1} A) g).app ((push A f).obj V)).app M ≫
      (push A g).map (((projectionMap (ModuleCat.{u + 1} A) f).app V).app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) =
    ((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app V).app M ≫
      (push A (f ≫ g)).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app M)) ≫
      k.hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M))) := by
  let C := (unboundedEtaleLowerShriekCompIso A f g).symm
  let N := ((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M))
  exact forward_projection_path (derivedTensor (ModuleCat.{u + 1} A) Z)
    C (unboundedEtaleLowerShriekCompIso A f g) rfl V N M
    (((projectionMap (ModuleCat.{u + 1} A) g).app ((push A f).obj V)).app M)
    ((push A g).map (((projectionMap (ModuleCat.{u + 1} A) f).app V).app
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)))
    (((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app V).app M)
    ((push A (f ≫ g)).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app M)))
    (projectionMap_chosen_comp A f g V M)

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem projection_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g]
    (V : DerivedCategoryModule A X) (M : DerivedCategoryModule A Z) :
    let k := rightDerivedLowerShriekCongrIso A (rfl : f ≫ g = f ≫ g) ≪≫
      rightDerivedLowerShriekCompIso A f g
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map (k.hom.app V)).app M ≫
      ((projectionMap (ModuleCat.{u + 1} A) g).app ((push A f).obj V)).app M ≫
      (push A g).map (((projectionMap (ModuleCat.{u + 1} A) f).app V).app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) =
    ((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app V).app M ≫
      (push A (f ≫ g)).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app M)) ≫
      k.hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M))) := by
  simpa only [Iso.symm_hom, composition_forward] using
    projection_square_forward A f g V M

end SourceConvention

/-- The canonical projection formula commutes with composition of proper maps.
Source: Stacks Project, Tags 0B56 and 0DV0; the concrete compactification calculation in
WeilConjectures.AlgebraicGeometry.ShriekTensorComposition, projectionMap_chosen_comp
(auxiliary; not a blueprint node).

Proof: first take r = f ≫ g. The concrete chosen-compactification projection square says
π_g; G(π_f); E = T(E); π_(fg); H(T(l)), where E is
unboundedEtaleLowerShriekCompIso and l is leftDerivedUpperStarComp. Expanding the three
comparison factors identifies E with the inverse of rightDerivedLowerShriekCompIso.
Precompose with T(C.hom), postcompose with C.hom, and cancel inverse pairs to get the
forward square below. Replace projectionMap.app by projectionIso.hom; the latter is the
asIso of exactly that map. For arbitrary r and hr, eliminate hr. The equality comparison
then becomes the identity isomorphism, so its extra factors disappear. This argument
neither specializes to a section nor uses a tensor unit or an identity projection law. -/
theorem properProjectionCompositionOfEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) [IsProper f] [IsProper g] [IsProper r] (hr : r = f ≫ g)
    (V : DerivedCategoryModule A X) (M : DerivedCategoryModule A Z) :
    let k := rightDerivedLowerShriekCongrIso A hr ≪≫ rightDerivedLowerShriekCompIso A f g
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map (k.hom.app V)).app M ≫
      (projectionIso A g ((push A f).obj V)).hom.app M ≫
      (push A g).map ((projectionIso A f V).hom.app ((CoordinateTrace.pull A g).obj M)) =
    (projectionIso A r V).hom.app M ≫
      (push A r).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g r hr).hom.app M)) ≫
      k.hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
        ((CoordinateTrace.pull A f).obj ((CoordinateTrace.pull A g).obj M))) := by
  subst r
  have h := projection_composition A f g V M
  dsimp only at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "no forward projection square"
    let eq ← (projectionCongr target (← Lean.instantiateMVars d.type)).run' {}
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

end AlgebraicGeometry.Etale.SupportedTrace
