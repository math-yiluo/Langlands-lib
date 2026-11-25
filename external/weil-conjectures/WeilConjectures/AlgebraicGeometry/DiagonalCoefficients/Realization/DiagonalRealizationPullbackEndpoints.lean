/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurRootTowerPreservation

/-! # Normalized endpoints for completed coefficient pullback

Source: diagonal coefficient changes, paragraph (3), endpoint construction.
(blueprint: lem-sfb-diagonal-realization-pullback-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

structure DiagonalRealizationPullbackEndpointData (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l) where
  completedUnit : (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) coeff).obj (SheafOfModules.unit
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))) ≅
      SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  completedLine : (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) coeff).obj (Scheme.purTwistZlModule S l) ≅
    Scheme.purTwistZlModule X l
  completedUnit_normalization : ∀ (U : S.ProEtᵒᵖ)
      (a : (Scheme.purTwistZlCompletion S l).obj.obj U),
    ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l)
      coeff).homEquiv _ _
        completedUnit.hom).val.app U a =
      (Scheme.proEtaleRingDirectImageMap f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l)
        coeff).hom.app U a
  completedLine_normalization : ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (z : (Scheme.purTwistZlOne S l).obj.obj U),
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
      (((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l)
        coeff).homEquiv _ _
          completedLine.hom).val.app U z) =
      (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
        ((limit.π (Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))
          (op n)).hom.app U z)

/-- The regular and whole-root endpoints have their specified adjoint normalizations.
Source: diagonal coefficient changes paragraph (3), proof steps 4 and 5.
(blueprint: lem-sfb-diagonal-realization-pullback-endpoints).

Proof: the normalized regular-module pullback isomorphism has the required
adjunct by its unit equation. Construct the whole-root comparison from the
canonical finite-root tower transformation: inverse image preserves this
particular tower and each finite comparison is invertible. Transpose its
projection equations under the abelian sheaf adjunction. The canonical
completed coefficient comparison has the matching finite coefficient projection
equations. The completed scalar action is coordinatewise, so finite-root
linearity and joint injectivity of the root-limit projections prove
semilinearity of the whole-root adjunct. Package it as a module direct-image
map and transpose under the module adjunction. Its underlying additive map
composed with the pullback unit mate is the whole-root comparison, by
adjunction injectivity. That unit mate is invertible when the coefficient
comparison is an isomorphism; the module forgetful functor reflects
isomorphisms. Thus the transposed module map is invertible, and its defining
adjunct gives the stated root normalization. -/
theorem diagonalRealization_pullback_endpoints (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    Nonempty (DiagonalRealizationPullbackEndpointData l f coeff) := by
  let residue (T : Scheme.{u}) (hu : IsUnit (l : Γ(T, ⊤))) :
      ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      let ψ := (T.residue x).hom.comp (T.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hu.map ψ).invertible
  let := residue X hX
  let := residue S hS
  let R := Scheme.purTwistZlCompletion S l
  let T := Scheme.purTwistZlCompletion X l
  let C : Scheme.FiniteFreeDirectImage.Coefficients f := ⟨R, T, coeff⟩
  let eu := Scheme.FiniteFreeDirectImage.pullbackRegularIso C
  let L := Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}
  let TS := Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)
  let TX := Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)
  obtain ⟨c, hcroot⟩ := (Scheme.proEtaleRootsOfUnityInverseImageIso f).2.1 l
    (Fact.out : l.Prime)
  have : ∀ j, IsIso (c.app j) := by
    intro j
    rw [hcroot j.unop]
    exact spRoots_cartesian f l (j.unop + 1)
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit TS L := Scheme.pur_root_tower_preservation f l
  let τ : L.obj (Scheme.purTwistZlOne S l) ⟶ Scheme.purTwistZlOne X l :=
    limit.post TS L ≫ lim.map c
  have hτi : IsIso τ := inferInstance
  have hτ (n : ℕ) : τ ≫ limit.π TX (op n) =
      L.map (limit.π TS (op n)) ≫
        Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)) := by
    change (limit.post TS L ≫ limMap c) ≫ limit.π TX (op n) = _
    rw [Category.assoc, limMap_π, limit.post_π_assoc, hcroot]
  let a := Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  let φ := (a.homEquiv _ _) τ
  have hroot (n : ℕ) (U : S.ProEtᵒᵖ) (z : (Scheme.purTwistZlOne S l).obj.obj U) :
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) (op n)).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U) (φ.hom.app U z) =
      (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
        ((limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out) (op n)).hom.app U z) := by
    have h := congrArg (a.homEquiv _ _) (hτ n)
    rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left] at h
    have hr : a.homEquiv _ _
        (Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1))) =
          Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)) :=
      (a.homEquiv _ _).apply_symm_apply _
    erw [hr] at h
    exact congrArg (fun k ↦ k.hom.app U z) h
  have hcoeff (n : ℕ) (U : S.ProEtᵒᵖ) (b : R.obj.obj U) :
      (Scheme.purTwistZlProjection X l n).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((Scheme.proEtaleRingDirectImageMap f R T coeff).hom.app U b) =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U
          ((Scheme.purTwistZlProjection S l n).hom.app U b) := by
    let ac := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
    have h : coeff.hom ≫ Scheme.purTwistZlProjection X l n =
        diagonalCompletedCoefficientComponent l f n := by
      rw [hc]
      exact limit.lift_π _ (op n)
    have h' := congrArg (ac.homEquiv _ _) h
    dsimp only [diagonalCompletedCoefficientComponent] at h'
    rw [ac.homEquiv_naturality_left, ac.homEquiv_naturality_right] at h'
    have hr : ac.homEquiv _ _
        (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) =
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) :=
      (ac.homEquiv _ _).apply_symm_apply _
    rw [hr] at h'
    exact congrArg (fun k ↦ k.hom.app U b) h'
  have action (Y : Scheme.{u}) (n : ℕ) (U : Y.ProEtᵒᵖ)
      (b : (Scheme.purTwistZlCompletion Y l).obj.obj U)
      (z : (Scheme.purTwistZlModule Y l).val.obj U) :
      (limit.π (Scheme.proEtaleRootsOfUnityTower Y l Fact.out) (op n)).hom.app U (b • z) =
        ((Scheme.purTwistZlProjection Y l n).hom.app U b) •
          (@id ((Scheme.purTwistRootsModule Y l n).val.obj U)
            ((limit.π (Scheme.proEtaleRootsOfUnityTower Y l Fact.out) (op n)).hom.app U z)) :=
    (Scheme.purTwistZlAction_existsUnique Y l).exists.choose_spec.2 n U b z
  have hscalar (U : S.ProEtᵒᵖ) (b : R.obj.obj U)
      (z : (Scheme.purTwistZlModule S l).val.obj U) :
      φ.hom.app U (b • z) =
        @SMul.smul _ _ (Scheme.purTwistZlAction X l
          ((Scheme.proEtaleBaseChange f).op.obj U)).toSMul
          ((Scheme.proEtaleRingDirectImageMap f R T coeff).hom.app U b)
          (φ.hom.app U z) := by
    let ev := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        ((Scheme.proEtaleBaseChange f).op.obj U)
    apply Concrete.isLimit_ext
      (Scheme.proEtaleRootsOfUnityTower X l Fact.out ⋙ ev)
      (isLimitOfPreserves ev (limit.isLimit _))
    intro n
    change (limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) n).hom.app _
        (φ.hom.app U (b • z)) =
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) n).hom.app _
        (@SMul.smul _ _ (Scheme.purTwistZlAction X l
          ((Scheme.proEtaleBaseChange f).op.obj U)).toSMul
          ((Scheme.proEtaleRingDirectImageMap f R T coeff).hom.app U b)
          (φ.hom.app U z))
    erw [hroot, action, action, hcoeff, hroot]
    have hs := ((rootModuleDirect f l n.unop).val.app U).hom.map_smul
      ((Scheme.purTwistZlProjection S l n.unop).hom.app U b)
      ((limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out) n).hom.app U z)
    change _ = @SMul.smul _ _
      ((Scheme.purTwistRootsModule X l n.unop).val.obj
        ((Scheme.proEtaleBaseChange f).op.obj U)).isModule.toSMul
      ((Scheme.proEtaleRingDirectImageMap f
        (Scheme.purTwistFiniteRing S l n.unop) (Scheme.purTwistFiniteRing X l n.unop)
        (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))) f)).hom.app U
          ((Scheme.purTwistZlProjection S l n.unop).hom.app U b))
      ((Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n.unop + 1))).hom.app U
        ((limit.π (Scheme.proEtaleRootsOfUnityTower S l Fact.out) n).hom.app U z)) at hs
    erw [constantStructural_direct] at hs
    exact hs
  let M := Scheme.purTwistZlModule S l
  let N := Scheme.purTwistZlModule X l
  let ψ : M ⟶ (Scheme.proEtaleRingModuleDirectImage f R T coeff).obj N :=
    { val :=
      { app := fun U ↦
          ConcreteCategory.ofHom
            (C := ModuleCat.{u + 1} ((Scheme.purTwistRing S R).obj.obj U))
            (X := M.val.obj U)
            (Y := ((Scheme.proEtaleRingModuleDirectImage f R T coeff).obj N).val.obj U)
            { toFun := fun z ↦ (φ.hom.app U).hom z
              map_add' := fun x y ↦ map_add (φ.hom.app U).hom x y
              map_smul' := fun b z ↦ hscalar U b z }
        naturality := by
          intro U V i
          ext z
          exact congrArg (fun k ↦ k.hom z) (φ.hom.naturality i) } }
  let adj := Scheme.proEtaleRingModuleAdjunction f R T coeff
  let t := (adj.homEquiv M N).symm ψ
  have ht : adj.homEquiv M N t = ψ := Equiv.apply_symm_apply _ _
  let UX := SheafOfModules.toSheaf (Scheme.purTwistRing X T)
  let US := SheafOfModules.toSheaf (Scheme.purTwistRing S R)
  let k := (a.homEquiv (US.obj M) (UX.obj
    ((Scheme.proEtaleRingModulePullback f R T coeff).obj M))).symm
      (US.map (adj.unit.app M))
  have hk : IsIso k := pullback_unit_mate_isIso f R T coeff M
  have he : k ≫ UX.map t = τ := by
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have h := ht
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun g ↦ US.map g) h
  have : IsIso (k ≫ UX.map t) := he.symm ▸ hτi
  have : IsIso (UX.map t) := IsIso.of_isIso_comp_left k _
  have : IsIso t := isIso_of_reflects_iso t UX
  refine ⟨{
    completedUnit := eu
    completedLine := asIso t
    completedUnit_normalization := ?_
    completedLine_normalization := ?_ }⟩
  · intro U b
    rw [Adjunction.homEquiv_unit]
    exact Scheme.FiniteFreeDirectImage.pullbackRegularIso_unit C U.unop b
  · intro n U z
    change (limit.π (Scheme.proEtaleRootsOfUnityTower X l Fact.out) (op n)).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)
      ((adj.homEquiv M N t).val.app U z) = _
    rw [ht]
    exact hroot n U z

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
