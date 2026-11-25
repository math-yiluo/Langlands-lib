/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRootPullIsIso
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRootPullStep

/-! # The finite root tower under inverse image

## References

* Bhatt--Scholze, Section 6.8
* Bhatt--Scholze, Section 6.8, finite roots and their power transition maps
* Stacks 03PK, pullback of roots of unity
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.PurityTransport

private noncomputable def mapFreeIso
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R] (M : C) :
    (F.mapMod R).obj ((Mod.freeFunctor R).obj M) ≅
      (Mod.freeFunctor (F.obj R)).obj (F.obj M) := by
  refine (Mod.isoMk (asIso (Functor.LaxMonoidal.μ F R M)) ?_).symm
  change ((α_ (F.obj R) (F.obj R) (F.obj M)).inv ≫
      (Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]) ▷ F.obj M) ≫
      Functor.LaxMonoidal.μ F R M =
    F.obj R ◁ Functor.LaxMonoidal.μ F R M ≫
      Functor.LaxMonoidal.μ F R (R ⊗ M) ≫
        F.map ((α_ R R M).inv ≫ μ[R] ▷ M)
  simp only [comp_whiskerRight, Functor.map_comp, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left,
    ← Functor.LaxMonoidal.associativity_inv_assoc]

private noncomputable def freeComapIso
    {C : Type*} [Category* C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a] [IsIso a] (M : C) :
    (Mod.freeFunctor R).obj M ≅ (Mod.comap a).obj ((Mod.freeFunctor S).obj M) := by
  refine Mod.isoMk (asIso (a ▷ M)) ?_
  change ((α_ R R M).inv ≫ μ[R] ▷ M) ≫ a ▷ M =
    R ◁ (a ▷ M) ≫ a ▷ (S ⊗ M) ≫ (α_ S S M).inv ≫ μ[S] ▷ M
  rw [Category.assoc, ← comp_whiskerRight, IsMonHom.mul_hom]
  simp only [MonoidalCategory.tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_left_assoc]

private theorem mapFreeIso_hom
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R] (M : C) :
    (mapFreeIso F R M).hom.hom = Functor.OplaxMonoidal.δ F R M := by
  simp [mapFreeIso, Mod.isoMk, Mod.homMk]

private theorem freeComapIso_inv
    {C : Type*} [Category* C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a] [IsIso a] (M : C) :
    (freeComapIso a M).inv.hom = inv a ▷ M := by
  simp [freeComapIso, Mod.isoMk, Mod.homMk]

private noncomputable def freePullIso
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] [IsIso a]
    {M : C} {N : D} (c : F.obj M ≅ N) :
    (Mod.comap (asIso a).inv).obj ((F.mapMod R).obj ((Mod.freeFunctor R).obj M)) ≅
      (Mod.freeFunctor S).obj N :=
  (Mod.comap (asIso a).inv).mapIso (mapFreeIso F R M) ≪≫
    (freeComapIso (asIso a).inv (F.obj M)).symm ≪≫ (Mod.freeFunctor S).mapIso c

private theorem freePullIso_hom
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] [IsIso a]
    {M : C} {N : D} (c : F.obj M ≅ N) :
    (freePullIso F R a c).hom.hom =
      Functor.OplaxMonoidal.δ F R M ≫ (a ⊗ₘ c.hom) := by
  simp only [freePullIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Mod.comp_hom', Mod.comap_map_hom, mapFreeIso_hom, freeComapIso_inv,
    asIso_inv, IsIso.inv_inv]
  change Functor.OplaxMonoidal.δ F R M ≫ a ▷ F.obj M ≫ S ◁ c.hom = _
  rw [MonoidalCategory.tensorHom_def]

private noncomputable def coefficientFreeIso
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf (ProEt.topology Y) Ab.{u + 1}}
    {N : Sheaf (ProEt.topology X) Ab.{u + 1}}
    (c : (upperStar Ab.{u + 1} f).obj M ≅ N) :
    (CondensedRing.upperStar R f).obj ((Mod.freeFunctor (condensedRingObj R Y)).obj M) ≅
      (Mod.freeFunctor (condensedRingObj R X)).obj N :=
  (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f)).app
      (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y)).obj
        ((Mod.freeFunctor (condensedRingObj R Y)).obj M)) ≪≫
    freePullIso (upperStar Ab.{u + 1} f) (condensedRingObj R Y)
      (condensedPullbackHom R f) c

private theorem coefficientFreeIso_normalized
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf (ProEt.topology Y) Ab.{u + 1}}
    {N : Sheaf (ProEt.topology X) Ab.{u + 1}}
    (c : (upperStar Ab.{u + 1} f).obj M ≅ N) :
    PullNormalized R f (coefficientFreeIso R f c)
      (Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj R Y) M ≫
        (condensedPullbackHom R f ⊗ₘ c.hom)) := by
  unfold PullNormalized
  apply heq_of_eq
  dsimp only [coefficientFreeIso, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  erw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact freePullIso_hom _ _ _ _

private noncomputable def freeRootSystem
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    (X : Scheme.{u}) (ell : ℕ) :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X) :=
  Functor.ofOpSequence
    (X := fun n ↦ (Mod.freeFunctor (condensedRingObj R X)).obj
      (rootsOfUnitySheaf X (ell ^ n)))
    (fun n ↦ (Mod.freeFunctor (condensedRingObj R X)).map
      (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ell ^ n) ell))

private noncomputable def freeRootTensorPull
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ell n : ℕ) :=
  Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f)
      (condensedRingObj R Y) (rootsOfUnitySheaf Y (ell ^ n)) ≫
    (condensedPullbackHom R f ⊗ₘ rootPull f (ell ^ n))

private noncomputable def levelIso
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (n : ℕ) :
    (CondensedRing.upperStar R f).obj
      ((Mod.freeFunctor (condensedRingObj R Y)).obj (rootsOfUnitySheaf Y (ell ^ n))) ≅
      (Mod.freeFunctor (condensedRingObj R X)).obj (rootsOfUnitySheaf X (ell ^ n)) := by
  have := normalizedRootPull_isIso ell f n
  exact coefficientFreeIso R f (asIso (rootPull f (ell ^ n)))

private theorem levelIso_normalized
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (n : ℕ) :
    PullNormalized R f (levelIso R ell f n) (freeRootTensorPull R f ell n) := by
  exact coefficientFreeIso_normalized _ _ _

private theorem freeRaw_naturality
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {R : C} {S : D} (a : F.obj R ⟶ S)
    {M N : C} {M' N' : D} (s : M ⟶ N) (t : M' ⟶ N')
    (b : F.obj M ⟶ M') (c : F.obj N ⟶ N')
    (h : F.map s ≫ c = b ≫ t) :
    F.map (R ◁ s) ≫ Functor.OplaxMonoidal.δ F R N ≫ (a ⊗ₘ c) =
      (Functor.OplaxMonoidal.δ F R M ≫ (a ⊗ₘ b)) ≫ S ◁ t := by
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, h]
  rw [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

private theorem normalized_square
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (U : C ⥤ D) (V : D ⥤ E) [V.Faithful] (W : C ⥤ E) (b : U ⋙ V ≅ W)
    {M N : C} {P Q : D} (s : M ⟶ N) (t : P ⟶ Q)
    (eM : U.obj M ⟶ P) (eN : U.obj N ⟶ Q)
    (cM : W.obj M ⟶ V.obj P) (cN : W.obj N ⟶ V.obj Q)
    (hM : b.inv.app M ≫ V.map eM = cM)
    (hN : b.inv.app N ≫ V.map eN = cN)
    (h : W.map s ≫ cN = cM ≫ V.map t) :
    U.map s ≫ eN = eM ≫ t := by
  apply V.map_injective
  apply (cancel_epi (b.inv.app M)).mp
  simp only [Functor.map_comp]
  change b.inv.app M ≫ (U ⋙ V).map s ≫ V.map eN =
    b.inv.app M ≫ V.map eM ≫ V.map t
  rw [← b.inv.naturality_assoc, hN, ← Category.assoc, hM]
  exact h

private theorem normalizedFreeRootTower
    [_hp : Precoherent Profinite.{u}]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃ e : freeRootSystem R Y ell ⋙ CondensedRing.upperStar R f ≅ freeRootSystem R X ell,
      ∀ n : ℕ, PullNormalized R f (e.app (Opposite.op n))
        (freeRootTensorPull R f ell n) := by
  let F := upperStar Ab.{u + 1} f
  let U := CondensedRing.upperStar R f
  let V := Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj R X)
  let b : U ⋙ V ≅ Mod.forget (condensedRingObj R Y) ⋙ F :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (F.mapMod (condensedRingObj R Y))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f))) V
  have hn (n : ℕ) : b.inv.app
      ((Mod.freeFunctor (condensedRingObj R Y)).obj (rootsOfUnitySheaf Y (ell ^ n))) ≫
      V.map (levelIso R ell f n).hom = freeRootTensorPull R f ell n :=
    eq_of_heq (levelIso_normalized R ell f n)
  let t : freeRootSystem R Y ell ⋙ U ⟶ freeRootSystem R X ell :=
    NatTrans.ofOpSequence (fun n ↦ (levelIso R ell f n).hom) (fun n ↦ by
      simp only [Functor.comp_map, freeRootSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply normalized_square U V (Mod.forget (condensedRingObj R Y) ⋙ F) b
        _ _ (levelIso R ell f (n + 1)).hom (levelIso R ell f n).hom
        (freeRootTensorPull R f ell (n + 1)) (freeRootTensorPull R f ell n)
        (hn (n + 1)) (hn n)
      exact freeRaw_naturality F (condensedPullbackHom R f) _ _ _ _
        (normalizedRootPull_step ell f n))
  have : ∀ n, IsIso (t.app n) := fun n ↦ (levelIso R ell f n.unop).isIso_hom
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, fun n ↦ levelIso_normalized R ell f n⟩



/- The definitions abstract class proofs into auxiliary constants.
Transport those proofs explicitly before comparing their induced category data;
a single conversion through all the six-functor definitions is prohibitively large.
The routines below only prepare congruences from Subsingleton.elim. -/
private def betaNormalize (e : Lean.Expr) (fuel : Nat) : Lean.Expr :=
  match fuel with
  | 0 => e
  | k + 1 =>
    match e with
    | .app f a => (Lean.Expr.app (betaNormalize f k) (betaNormalize a k)).headBeta
    | .lam n t v bi => .lam n (betaNormalize t k) (betaNormalize v k) bi
    | .forallE n t v bi => .forallE n (betaNormalize t k) (betaNormalize v k) bi
    | .mdata _ v => betaNormalize v k
    | _ => e

private def firstProofDifference (a b : Lean.Expr) (fuel : Nat) :
    Lean.Meta.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  match fuel with
  | 0 => return none
  | k + 1 =>
    if a == b then return none
    if !a.hasLooseBVars && !b.hasLooseBVars &&
        (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) &&
        (← Lean.Meta.isDefEq (← Lean.Meta.inferType a) (← Lean.Meta.inferType b)) then
      return some (a, b)
    match a, b with
    | .app f x, .app h y =>
      if let some p ← firstProofDifference f h k then return some p
      firstProofDifference x y k
    | .lam _ t v _, .lam _ u w _ | .forallE _ t v _, .forallE _ u w _ =>
      if let some p ← firstProofDifference t u k then return some p
      firstProofDifference v w k
    | _, _ => return none

/-- The finite root pullbacks form an isomorphism of the actual integral root diagrams. -/
theorem normalizedRootTower (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃ e : tateModuleSystem Y ell ⋙
        CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f ≅
      tateModuleSystem X ell,
      ∀ n : ℕ, PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f
        (e.app (Opposite.op n)) (rootTensorPull ell f n) := by
  have h := normalizedFreeRootTower (Profinite.continuousMapRingObj ℤ_[ell]) ell f
  dsimp only [freeRootSystem, tateModuleSystem, tateModuleLevel, tateModuleTransition,
    freeRootTensorPull, rootTensorPull, condensedPullbackHom, Functor.compAlgHom,
    condensedRingObj] at h ⊢
  -- Identify the stored proof instances by congruence, on both propositions.
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let target ← Lean.instantiateMVars (← g.getType)
      let h ← Lean.Meta.getLocalDeclFromUserName `h
      let mut lhs := betaNormalize h.type 400
      let mut rhs := betaNormalize target 400
      let mut eqL ← Lean.Meta.mkEqRefl lhs
      let mut eqR ← Lean.Meta.mkEqRefl rhs
      let mut canonical : Array Lean.Expr := #[]
      for _ in [:100] do
        if lhs == rhs then break
        let some (p, q) ← firstProofDifference lhs rhs 400 | break
        let mut c := p
        let mut found := false
        for a in canonical do
          if ← Lean.Meta.isDefEq (← Lean.Meta.inferType p) (← Lean.Meta.inferType a) then
            c := a
            found := true
            break
        if !found then canonical := canonical.push p
        for which in [true, false] do
          for old in [p, q] do
            let cur := if which then lhs else rhs
            if old == c then continue
            let next := betaNormalize (cur.replace (fun t => if t == old then some c else none)) 400
            if next == cur then continue
            let motive ← Lean.Meta.withLocalDeclD `proofArg (← Lean.Meta.inferType old)
                fun x => Lean.Meta.mkLambdaFVars #[x]
                  (cur.replace (fun t => if t == old then some x else none))
            let peq ← Lean.Meta.mkAppM ``Subsingleton.elim #[old, c]
            let eq ← Lean.Meta.mkAppM ``congrArg #[motive, peq]
            if which then
              eqL ← Lean.Meta.mkAppM ``Eq.trans #[eqL, eq]
              lhs := next
            else
              eqR ← Lean.Meta.mkAppM ``Eq.trans #[eqR, eq]
              rhs := next
      unless ← Lean.Meta.isDefEq lhs rhs do
        throwError "remaining data difference"
      let eq ← Lean.Meta.mkAppM ``Eq.trans #[eqL, ← Lean.Meta.mkAppM ``Eq.symm #[eqR]]
      let pf ← Lean.Meta.mkAppM ``Eq.mp #[eq, h.toExpr]
      g.assign pf
      Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.PurityTransport
