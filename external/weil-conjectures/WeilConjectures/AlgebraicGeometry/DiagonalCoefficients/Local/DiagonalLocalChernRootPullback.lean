/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernPullbackData
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientConePush
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLinePullbackLowerTensor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Root cone in the horizontal completed Chern square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory

open WeilConjectures

attribute [local irreducible] SemilinearSections.scalarExtensionSection
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau
  Functor.ofOpSequence Functor.ofSequence SemilinearSections.evaluation

-- Prove the carrier transports before specializing to the scalar-extended line.
private theorem restrictionUnderlying_hom_section
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ)
    (x : ((r.F.obj M).obj (op n)).obj.obj U) :
    HEq (((restrictionUnderlying l T r n).hom.app M).hom.app U x) x :=
  finiteBoundary_cast_heq (r.underlying M n U) x

private theorem restrictionUnderlying_inv_section
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj M).val.obj U) :
    HEq (((restrictionUnderlying l T r n).inv.app M).hom.app U x) x :=
  finiteBoundary_cast_heq (r.underlying M n U).symm x

private theorem restrictionUnderlying_hom_injective
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ) :
    Function.Injective (((restrictionUnderlying l T r n).hom.app M).hom.app U) := by
  intro x y h
  exact eq_of_heq ((restrictionUnderlying_hom_section l T r n M U x).symm.trans
    ((heq_of_eq h).trans (restrictionUnderlying_hom_section l T r n M U y)))

private theorem finiteEvaluationSection_exists
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (U : T.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ∃ v : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) T n).obj M).val.obj U,
      HEq v x := ⟨x, HEq.rfl⟩

private def moduleIsoSectionEquiv
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (U : Cᵒᵖ) : M.val.obj U ≃ N.val.obj U where
  toFun := e.hom.val.app U
  invFun := e.inv.val.app U
  left_inv x := congrArg (fun q : M ⟶ M ↦ q.val.app U x) e.hom_inv_id
  right_inv x := congrArg (fun q : N ⟶ N ↦ q.val.app U x) e.inv_hom_id

private theorem constantPushforward_map_heq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    (a : M ⟶ N) (U : Y.ProEtᵒᵖ) (x : M.val.obj (chart f U))
    (y : ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U)
    (hxy : HEq x y) :
    a.val.app (chart f U) x =
      ((Scheme.proEtaleConstantRingPushforward A f).map a).val.app U y := by
  have h : x = y := eq_of_heq hxy
  cases h
  exact (pushforward_map_apply A f a U x).symm

-- Compare the scalar-extension root section with its normalized finite evaluation.
private theorem normalizedRootSection
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj U) :
    (lineEvaluation l (ULift.{u} (Padic l)) c n).hom.val.app U
      (((restrictionUnderlying l T r n).hom.app
        (lineModule l (ULift.{u} (Padic l)) c)).hom.app U
        ((k.lineForget.inv.app (op n)).hom.app U z)) =
      Scheme.tateFiniteTensor T l (FiniteRing l (ULift.{u} (Padic l)) n) n
        (finiteScalar l (ULift.{u} (Padic l)) n) U.unop 1 z := by
  let x' := (c.rootForget.inv.app (op n)).hom.app U z
  let x : c.rootModule.val.obj (op (n, U.unop)) :=
    (eqToHom (c.reduction.forget.sections c.rootModule n U)) x'
  have hx : HEq x' x := (finiteBoundary_cast_heq
    (c.reduction.forget.sections c.rootModule n U) x').symm
  obtain ⟨v, hv⟩ := finiteEvaluationSection_exists l T n
    (lineModule l (ULift.{u} (Padic l)) c) U
    (SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
      (coefficientSystemMap l (ULift.{u} (Padic l)) T) c.scalar c.rootModule
      (op (n, U.unop)) x)
  let w := ((restrictionUnderlying l T r n).inv.app
    (lineModule l (ULift.{u} (Padic l)) c)).hom.app U v
  have hw : HEq w v := restrictionUnderlying_inv_section l T r n
    (lineModule l (ULift.{u} (Padic l)) c) U v
  have ht := k.line_tensor n U x x' w hx.symm (hw.trans hv)
  have hz := (addSectionEquiv (c.rootForget.app (op n)) U).apply_symm_apply z
  have hw' : w = (k.lineForget.inv.app (op n)).hom.app U z := by
    exact (addSectionEquiv (k.lineForget.app (op n)) U).injective
      ((ht.trans hz).trans
        ((addSectionEquiv (k.lineForget.app (op n)) U).apply_symm_apply z).symm)
  have hwv : ((restrictionUnderlying l T r n).hom.app
      (lineModule l (ULift.{u} (Padic l)) c)).hom.app U w = v :=
    eq_of_heq ((restrictionUnderlying_hom_section l T r n
      (lineModule l (ULift.{u} (Padic l)) c) U w).trans hw)
  have hnorm := (lineEvaluation_existsUnique l (ULift.{u} (Padic l)) c n).exists.choose_spec
    U 1 x x' v hx.symm
    (by simpa only [one_smul] using hv)
  have hsection := (congrArg
    (((restrictionUnderlying l T r n).hom.app
      (lineModule l (ULift.{u} (Padic l)) c)).hom.app U) hw'.symm).trans hwv
  exact (congrArg ((lineEvaluation l (ULift.{u} (Padic l)) c n).hom.val.app U)
    hsection).trans (hnorm.trans (congrArg
      (Scheme.tateFiniteTensor T l (FiniteRing l (ULift.{u} (Padic l)) n) n
        (finiteScalar l (ULift.{u} (Padic l)) n) U.unop 1) hz))

-- Transport a module morphism before specializing to Chern-line modules.
private theorem varyingPush_adjoint_section
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (d : LocalChernPullbackData l hX p p') (n : ℕ)
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X))
    (N : Systems X' (Arings l (ULift.{u} (Padic l)) X'))
    (a : d.geometry.pull.obj M ⟶ N) (U : X.ProEtᵒᵖ)
    (y : ((p.restrictionX.F.obj M).obj (op n)).obj.obj U)
    (x : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) X n).obj M).val.obj U)
    (hx : HEq y x) :
    HEq (((d.varyingPush.hom.app N).app (op n)).hom.app U
      (((p.restrictionX.F.map (d.geometry.ordinaryAdjunction.homEquiv M N a)).app
        (op n)).hom.app U y))
      (adjointSection l (ULift.{u} (Padic l)) d.geometry a n U x) := by
  let α := d.geometry.ordinaryAdjunction.homEquiv M N a
  have hα := additive_transport_apply
    (p.restrictionX.underlying M n U)
    (p.restrictionX.underlying (d.geometry.push.obj N) n U)
    (AddCommGrpCat.ofHom
      ((((p.restrictionX.F.map α).app (op n)).hom.app U).hom.toAddMonoidHom))
    (AddCommGrpCat.ofHom ((α.val.app (op (n, U.unop))).hom.toAddMonoidHom))
    (p.restrictionX.morphisms α n U) y x hx
  have hp := push_sections l (ULift.{u} (Padic l)) d.base d.geometry n N U
    ((α.val.app (op (n, U.unop))) x)
  exact (d.varyingPush_sections N n U _).trans (hα.trans hp.symm)

-- Compare the line sections in the two scalar restrictions and finite evaluations.
private theorem horizontal_varying_root_square
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (d : LocalChernPullbackData l hX p p') (n : ℕ) :
    let α := d.geometry.ordinaryAdjunction.homEquiv _ _ d.line.iso.hom
    (diagonalForget l X).map
        ((p.restrictionX.F.map α ≫ d.varyingPush.hom.app
          (lineModule l (ULift.{u} (Padic l)) p'.chernX)).app (op n)) ≫
      (lowerStar AddCommGrpCat.{u + 1} hX).map
        (p'.coefficientsX.lineForget.hom.app (op n)) =
    p.coefficientsX.lineForget.hom.app (op n) ≫
      Scheme.proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1)) := by
  dsimp only
  apply (cancel_epi (p.coefficientsX.lineForget.inv.app (op n))).mp
  apply Sheaf.hom_ext
  ext U z
  let N := lineModule l (ULift.{u} (Padic l)) p.chernX
  let N' := lineModule l (ULift.{u} (Padic l)) p'.chernX
  let α := d.geometry.ordinaryAdjunction.homEquiv _ _ d.line.iso.hom
  let y := (p.coefficientsX.lineForget.inv.app (op n)).hom.app U z
  let x : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) X n).obj N).val.obj U :=
    (((restrictionUnderlying l X p.restrictionX n).hom.app N).hom.app U) y
  have hx : HEq y x :=
    (restrictionUnderlying_hom_section l X p.restrictionX n N U y).symm
  have hcoord := normalizedRootSection l X p.chernX p.restrictionX p.coefficientsX n U z
  have hinput :=
    (moduleIsoSectionEquiv (lineEvaluation l (ULift.{u} (Padic l)) p.chernX n) U).eq_symm_apply.mpr
      hcoord
  dsimp only [moduleIsoSectionEquiv, Equiv.symm, Equiv.coe_fn_mk] at hinput
  let v := (((d.varyingPush.hom.app N').app (op n)).hom.app U)
    (((p.restrictionX.F.map α).app (op n)).hom.app U y)
  have hv : HEq v (adjointSection l (ULift.{u} (Padic l)) d.geometry
      d.line.iso.hom n U x) :=
    varyingPush_adjoint_section l hX p p' d n N N' d.line.iso.hom U y x hx
  let U' := chart hX U
  let x' : ((SpTowerShriek.ev l (ULift.{u} (Padic l)) X' n).obj N').val.obj U' :=
    (((restrictionUnderlying l X' p'.restrictionX n).hom.app N').hom.app U') v
  have hx' : HEq x' (adjointSection l (ULift.{u} (Padic l)) d.geometry
      d.line.iso.hom n U x) := by
    exact (restrictionUnderlying_hom_section l X' p'.restrictionX n N' U' v).trans hv
  dsimp only [x, N, y] at hx'
  have heval := d.line.normalization n U 1 z
  rw [← hinput, map_one] at heval
  have hmap := constantPushforward_map_heq (SpTowerShriek.R l (ULift.{u} (Padic l)) n) hX
    (lineEvaluation l (ULift.{u} (Padic l)) p'.chernX n).hom U x' _ hx'
  rw [← hmap] at heval
  let z' := (p'.coefficientsX.lineForget.hom.app (op n)).hom.app U' v
  have hroot : z' = restrictRoot l hX n U z := by
    have hleft := normalizedRootSection l X' p'.chernX p'.restrictionX
      p'.coefficientsX n U' (restrictRoot l hX n U z)
    have heinj :=
      (moduleIsoSectionEquiv (lineEvaluation l (ULift.{u} (Padic l)) p'.chernX n) U').injective
    have hxv := heinj (heval.trans hleft.symm)
    dsimp only [x', N'] at hxv
    have hv' := restrictionUnderlying_hom_injective l X' p'.restrictionX n
      (lineModule l (ULift.{u} (Padic l)) p'.chernX) U' hxv
    have hzv := congrArg
      (fun q ↦ (p'.coefficientsX.lineForget.hom.app (op n)).hom.app U' q) hv'
    have hir := (addSectionEquiv (p'.coefficientsX.lineForget.app (op n)) U').apply_symm_apply
      (restrictRoot l hX n U z)
    exact hzv.trans hir
  have hiS := (addSectionEquiv (p.coefficientsX.lineForget.app (op n)) U).apply_symm_apply z
  change (p'.coefficientsX.lineForget.hom.app (op n)).hom.app U' v =
    (Scheme.proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1))).hom.app U
      ((p.coefficientsX.lineForget.hom.app (op n)).hom.app U y)
  have hr : (Scheme.proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1))).hom.app U z =
      restrictRoot l hX n U z := by
    apply (Scheme.proEtaleRootsOfUnitySections X' (l ^ (n + 1))
      (chart hX U)).injective
    rw [restrictRoot, AddEquiv.apply_symm_apply]
    have hr :=
      (Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1))).exists
    exact hr.choose_spec U z
  exact hroot.trans (hr.symm.trans (congrArg
    ((Scheme.proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1))).hom.app U) hiS.symm))

-- Identify the completed and varying root cones through their actual finite projections.
private theorem horizontal_root_cone_transposed
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') (n : ℕ) :
    let a := (Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))).homEquiv
        (Scheme.purTwistZlModule X l) (Scheme.purTwistZlModule X' l) r.completedLine.hom
    let t := d.geometry.ordinaryAdjunction.homEquiv _ _ d.line.iso.hom
    (diagonalCompletedRestriction l X).map a ≫
      d.completedPush.hom.app (Scheme.purTwistZlModule X' l) ≫
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).map
        (p'.coefficientsX.lineProjection.app (op n)) =
    p.coefficientsX.lineProjection.app (op n) ≫
      (p.restrictionX.F.map t ≫ d.varyingPush.hom.app
        (lineModule l (ULift.{u} (Padic l)) p'.chernX)).app (op n) := by
  dsimp only
  have : (diagonalForget l X).Faithful := by unfold diagonalForget; infer_instance
  apply (diagonalForget l X).map_injective
  apply (cancel_mono ((lowerStar AddCommGrpCat.{u + 1} hX).map
    (p'.coefficientsX.lineForget.hom.app (op n)))).mp
  ext U z
  let y := (((diagonalCompletedRestriction l X).map
    ((Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))).homEquiv _ _
        r.completedLine.hom)).hom.app U) z
  let v := (d.completedPush.hom.app (Scheme.purTwistZlModule X' l)).hom.app U y
  have hp := p'.coefficientsX.line_projection n
    ((Scheme.proEtaleBaseChange hX).op.obj U) v
  have hβ := congrArg (fun q ↦ q.hom.app U
    ((p.coefficientsX.lineProjection.app (op n)).hom.app U z))
      (horizontal_varying_root_square l hX p p' d n)
  change (p'.coefficientsX.lineForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange hX).op.obj U)
      (((p.restrictionX.F.map
        (d.geometry.ordinaryAdjunction.homEquiv _ _ d.line.iso.hom) ≫
          d.varyingPush.hom.app _).app (op n)).hom.app U
          ((p.coefficientsX.lineProjection.app (op n)).hom.app U z)) =
    (Scheme.proEtaleRootsOfUnityDirectImageMap hX (l ^ (n + 1))).hom.app U
      ((p.coefficientsX.lineForget.hom.app (op n)).hom.app U
        ((p.coefficientsX.lineProjection.app (op n)).hom.app U z)) at hβ
  rw [p.coefficientsX.line_projection] at hβ
  have hv : v = ((Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))).homEquiv _ _
        r.completedLine.hom).val.app U z := by
    exact eq_of_heq (d.completedPush_sections _ U y)
  change (p'.coefficientsX.lineForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange hX).op.obj U)
      ((p'.coefficientsX.lineProjection.app (op n)).hom.app
        ((Scheme.proEtaleBaseChange hX).op.obj U) v) = _
  rw [hp, hv, r.completedLine_normalization]
  exact hβ.symm

private theorem scalar_mate_homEquiv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : A ⥤ C) (H : B ⥤ D)
    (s : G ⋙ L' ≅ L ⋙ H) {M : A} {N : B} (m : L.obj M ⟶ N) :
    (adj'.homEquiv (G.obj M) (H.obj N)) (s.hom.app M ≫ H.map m) =
      G.map ((adj.homEquiv M N) m) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).app N := by
  let β := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom))
  have hn := β.naturality m
  simp only [Functor.comp_map] at hn
  have hu := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom) M
  change G.map (adj.unit.app M) ≫ β.app (L.obj M) =
    adj'.unit.app (G.obj M) ≫ R'.map (s.hom.app M) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% hu]

private theorem horizontal_root_cone
    (l : ℕ) [Fact l.Prime] {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') :
    let M := Scheme.purTwistZlModule X l
    let N := lineModule l (ULift.{u} (Padic l)) p.chernX
    (Functor.const ℕᵒᵖ).map (d.completedOrdinary.hom.app M ≫
        (diagonalCompletedRestriction l X').map r.completedLine.hom) ≫
      p'.coefficientsX.lineProjection =
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).mapCone (Cone.mk _
        p.coefficientsX.lineProjection)).π ≫
      d.varyingOrdinary.hom.app N ≫ p'.restrictionX.F.map d.line.iso.hom := by
  dsimp only
  apply NatTrans.ext
  funext n
  let adj := upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX
  have hc := scalar_mate_homEquiv
    (Scheme.proEtaleRingModuleAdjunction hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX))) adj
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l X')
    d.completedOrdinary r.completedLine.hom
  have hv := scalar_mate_homEquiv d.geometry.ordinaryAdjunction
    (adj.whiskerRight ℕᵒᵖ) p.restrictionX.F p'.restrictionX.F
    d.varyingOrdinary d.line.iso.hom
  have hcm := d.completedMate
  have hvm := d.varyingMate
  dsimp only [adj] at hc hv
  rw [hcm] at hc
  rw [hvm] at hv
  have hvn := congrArg (fun q ↦ q.app n) hv
  simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app] at hvn
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ ((d.completedOrdinary.hom.app _ ≫
      (diagonalCompletedRestriction l X').map r.completedLine.hom) ≫
      p'.coefficientsX.lineProjection.app n) =
    adj.homEquiv _ _ (((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).map
      (p.coefficientsX.lineProjection.app n) ≫
      (d.varyingOrdinary.hom.app _).app n ≫
      (p'.restrictionX.F.map d.line.iso.hom).app n)
  rw [Adjunction.homEquiv_naturality_right, hc,
    Adjunction.homEquiv_naturality_left]
  rw [show adj.homEquiv _ _ ((d.varyingOrdinary.hom.app _).app n ≫
      (p'.restrictionX.F.map d.line.iso.hom).app n) = _ from hvn]
  simpa only [Category.assoc, NatTrans.comp_app, Adjunction.homEquiv_unit,
    Opposite.op_unop] using
    horizontal_root_cone_transposed l hX p p' eX eX' r d n.unop

-- The ordinary cone has been identified; derived transport needs only its interface.
attribute [local irreducible] DerivedCategory Scheme.purTwistZlModule
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem single_tower_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℤ) :
    DerivedCategory.singleFunctor (SpTowerShriek.S l (ULift.{u} (Padic l)) X) n =
      DerivedCategory.singleFunctor (Systems X (Arings l (ULift.{u} (Padic l)) X)) n := by
  rfl
private theorem shift_tower_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℤ) :
    shiftFunctor (DerivedCategory (SpTowerShriek.S l (ULift.{u} (Padic l)) X)) n =
      shiftFunctor (DerivedCategory (Systems X (Arings l (ULift.{u} (Padic l)) X))) n := by
  rfl

private theorem ordinaryRlim_naturality
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) {H K : ℕᵒᵖ ⥤ A} (b : H ⟶ K) :
    (DerivedCategory.singleFunctor A 0).map ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).map b) ≫
        diagonalOrdinaryRlim L K =
      diagonalOrdinaryRlim L H ≫
        L.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map b) := by
  let α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ DerivedCategory.singleFunctor A 0 ⟶
      DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0 ⋙ L.R :=
    Functor.whiskerLeft lim (DerivedCategory.singleFunctorIsoCompQ A 0).hom ≫
      Functor.whiskerRight
        (HomologicalComplex.singleMapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (.up ℤ) 0).inv DerivedCategory.Q ≫
      Functor.whiskerLeft (HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0) L.η ≫
      Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ A) 0).inv L.R
  exact α.naturality b

private theorem traceCone_naturality
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) {H K : ℕᵒᵖ ⥤ A} (c : Cone H) (d : Cone K)
    (a : c.pt ⟶ d.pt) (b : H ⟶ K)
    (hab : c.π ≫ b = (Functor.const ℕᵒᵖ).map a ≫ d.π) :
    (DerivedCategory.singleFunctor A 0).map a ≫ diagonalTraceConeMap L K d =
      diagonalTraceConeMap L H c ≫
        L.R.map ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).map b) := by
  have hlift : a ≫ limit.lift K d =
      limit.lift H c ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).map b := by
    apply limit.hom_ext
    intro n
    have h := congrArg (fun t ↦ t.app n) hab
    simp only [Category.assoc, limit.lift_π]
    erw [limMap_π, limit.lift_π_assoc]
    exact h.symm
  unfold diagonalTraceConeMap
  rw [← Category.assoc, ← Functor.map_comp, hlift, Functor.map_comp, Category.assoc,
    ordinaryRlim_naturality]
  simp only [Category.assoc]

private theorem exactSquare_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V) (M : A) :
    (Functor.mapDerivedCategorySquareIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      V.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
    P.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (s.hom.app M) := by
  unfold Functor.mapDerivedCategorySquareIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U P).inv.app
    ((DerivedCategory.singleFunctor A 0).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U P M)]

-- Normalize the two exact single squares and the full derived-limit cone equation.
private theorem exactConeComparison_transport
    {A B C D E E' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category E']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian E']
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (U : A ⥤ B) (H : A ⥤ C) (U' : C ⥤ D) (P : B ⥤ D)
    (V : E ⥤ ℕᵒᵖ ⥤ B) (G : E ⥤ E') (V' : E' ⥤ ℕᵒᵖ ⥤ D)
    [U.Additive] [H.Additive] [U'.Additive] [P.Additive]
    [V.Additive] [G.Additive] [V'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    (s : U ⋙ P ≅ H ⋙ U')
    (t : V ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj P ≅ G ⋙ V')
    (L : DiagonalRlim B) (L' : DiagonalRlim D)
    (β : L.R ⋙ P.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory ⋙ L'.R)
    {M : A} {M' : C} {N : E} {N' : E'}
    (m : H.obj M ⟶ M') (n : G.obj N ⟶ N')
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N)
    (π' : (Functor.const ℕᵒᵖ).obj (U'.obj M') ⟶ V'.obj N')
    (hπ : (P.mapCone (Cone.mk _ π)).π ≫ t.hom.app N ≫ V'.map n =
      (Functor.const ℕᵒᵖ).map (s.hom.app M ≫ U'.map m) ≫ π')
    (hβ : P.mapDerivedCategory.map (diagonalTraceConeMap L (V.obj N) (Cone.mk _ π)) ≫
      β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (V.obj N)) ≫
      L'.R.map ((Functor.mapDerivedCategorySingleFunctor
        ((Functor.whiskeringRight ℕᵒᵖ B D).obj P) 0).hom.app (V.obj N)) =
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      diagonalTraceConeMap L' _ (P.mapCone (Cone.mk _ π))) :
    (Functor.mapDerivedCategorySquareIso s).inv.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      P.mapDerivedCategory.map (exactConeComparison U V L M N π) ≫
      β.app (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor E 0).obj N)) ≫
      L'.R.map ((Functor.mapDerivedCategorySquareIso t).hom.app
        ((DerivedCategory.singleFunctor E 0).obj N)) ≫
      L'.R.map (V'.mapDerivedCategory.map
        ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor E' 0).map n)) =
    U'.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map m) ≫
      exactConeComparison U' V' L' M' N' π' := by
  let W := (Functor.whiskeringRight ℕᵒᵖ B D).obj P
  have hn := (V'.mapDerivedCategorySingleFunctor 0).hom.naturality n
  have hm := (U'.mapDerivedCategorySingleFunctor 0).hom.naturality m
  have hnat := β.naturality ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
  simp only [Functor.comp_map] at hn hm hnat
  have hc := traceCone_naturality L' (P.mapCone (Cone.mk _ π)) (Cone.mk _ π')
    (s.hom.app M ≫ U'.map m) (t.hom.app N ≫ V'.map n) hπ
  have hsource : exactConeComparison U V L M N π =
      (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        diagonalTraceConeMap L (V.obj N) (Cone.mk _ π) ≫
        L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N) := by
    simp only [exactConeComparison, diagonalTraceConeMap, Category.assoc]
  have htarget : exactConeComparison U' V' L' M' N' π' =
      (U'.mapDerivedCategorySingleFunctor 0).hom.app M' ≫
        diagonalTraceConeMap L' (V'.obj N') (Cone.mk _ π') ≫
        L'.R.map ((V'.mapDerivedCategorySingleFunctor 0).inv.app N') := by
    simp only [exactConeComparison, diagonalTraceConeMap, Category.assoc]
  rw [hsource, htarget]
  apply (cancel_mono (L'.R.map ((V'.mapDerivedCategorySingleFunctor 0).hom.app N'))).mp
  simp only [Functor.map_comp, Category.assoc]
  conv_rhs => simp only [← L'.R.map_comp, Iso.inv_hom_id_app]
  erw [L'.R.map_id, Category.comp_id]
  rw [← L'.R.map_comp, ← L'.R.map_comp, hn]
  rw [← L'.R.map_comp, reassoc_of% (exactSquare_single V W G V' t N)]
  simp only [Functor.map_comp]
  rw [reassoc_of% hnat]
  rw [← L'.R.map_comp_assoc, ← W.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  erw [W.mapDerivedCategory.map_id, L'.R.map_id, Category.id_comp]
  rw [reassoc_of% hβ]
  rw [← L'.R.map_comp, ← (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map_comp,
    ← hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (exactSquare_single U P H U' s M)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hm]

private theorem exactConeComparison_transport_associated
    {A B C D E E' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category E']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian E']
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (U : A ⥤ B) (H : A ⥤ C) (U' : C ⥤ D) (P : B ⥤ D)
    (V : E ⥤ ℕᵒᵖ ⥤ B) (G : E ⥤ E') (V' : E' ⥤ ℕᵒᵖ ⥤ D)
    [U.Additive] [H.Additive] [U'.Additive] [P.Additive]
    [V.Additive] [G.Additive] [V'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    (s : U ⋙ P ≅ H ⋙ U')
    (t : V ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj P ≅ G ⋙ V')
    (L : DiagonalRlim B) (L' : DiagonalRlim D)
    (β : L.R ⋙ P.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory ⋙ L'.R)
    {M : A} {M' : C} {N : E} {N' : E'}
    (m : H.obj M ⟶ M') (n : G.obj N ⟶ N')
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N)
    (π' : (Functor.const ℕᵒᵖ).obj (U'.obj M') ⟶ V'.obj N')
    (hπ : (P.mapCone (Cone.mk _ π)).π ≫ t.hom.app N ≫ V'.map n =
      (Functor.const ℕᵒᵖ).map (s.hom.app M ≫ U'.map m) ≫ π')
    -- Packaged, so that the kernel matches `LocalChernPullbackData.cone` by its arguments
    -- instead of unfolding the two presentations of the strict systems.
    (hβ : LocalChernConeMate P L L' β) :
    (Functor.mapDerivedCategorySquareIso s).inv.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      P.mapDerivedCategory.map (exactConeComparison U V L M N π) ≫
      ((Functor.associator V.mapDerivedCategory L.R P.mapDerivedCategory).hom ≫
        Functor.whiskerLeft V.mapDerivedCategory β ≫
        (Functor.associator V.mapDerivedCategory
          ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory L'.R).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso t).hom L'.R ≫
        (Functor.associator G.mapDerivedCategory V'.mapDerivedCategory L'.R).hom).app
          ((DerivedCategory.singleFunctor E 0).obj N) ≫
      L'.R.map (V'.mapDerivedCategory.map
        ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor E' 0).map n)) =
    U'.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor C 0).map m) ≫
      exactConeComparison U' V' L' M' N' π' := by
  have ht := exactConeComparison_transport U H U' P V G V' s t L L' β m n π π' hπ
    (hβ _ (Cone.mk _ π))
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using ht

private theorem line_derivedIso_eq
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    {b : SpTowerShriek.Base l (ULift.{u} (Padic l))}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f}
    {cY : Chern l (ULift.{u} (Padic l)) Y}
    {cX : Chern l (ULift.{u} (Padic l)) X}
    (q : LinePullback l (ULift.{u} (Padic l)) f g cY cX) :
    (q.derivedIso l (ULift.{u} (Padic l))).hom =
      (g.pull.mapDerivedCategorySingleFunctor 0).hom.app
          (lineModule l (ULift.{u} (Padic l)) cY) ≫
        (DerivedCategory.singleFunctor (Systems X (Arings l (ULift.{u} (Padic l)) X)) 0).map
          q.iso.hom := by
  rfl

-- Instantiate cone transport on the independently normalized root systems.
private theorem horizontal_root_unshifted (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (_hunit : IsUnit (l : Γ(X, ⊤))) (_hunit' : IsUnit (l : Γ(X', ⊤)))
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') :
      (d.completedSquare l).inv.app (completedLine l X) ≫
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory.map
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) ≫
        (d.comparison l).app (SpTowerClasses.line l (ULift.{u} (Padic l)) p.chernX) ≫
        p'.LX.R.map (p'.restrictionX.F.mapDerivedCategory.map
          (d.line.derivedIso l (ULift.{u} (Padic l))).hom) =
      (diagonalCompletedUnderlying l X').map
        (diagonalRealizationPullSingle l hX r.completedLine).hom ≫
        p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX := by
  let := d.geometry.pullAdditive
  let := d.geometry.pullLimits
  let := d.geometry.pullColimits
  let := p.restrictionX.additive
  let := p.restrictionX.limits
  let := p.restrictionX.colimits
  let := p'.restrictionX.additive
  let := p'.restrictionX.limits
  let := p'.restrictionX.colimits
  let : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)) := d.towerLimits
  let : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)) := d.towerColimits
  have hπ := horizontal_root_cone l hX p p' eX eX' r d
  have ht := exactConeComparison_transport_associated
    (E := Systems X (Arings l (ULift.{u} (Padic l)) X))
    (E' := Systems X' (Arings l (ULift.{u} (Padic l)) X'))
    (M := Scheme.purTwistZlModule X l) (M' := Scheme.purTwistZlModule X' l)
    (N := lineModule l (ULift.{u} (Padic l)) p.chernX)
    (N' := lineModule l (ULift.{u} (Padic l)) p'.chernX)
    (diagonalCompletedRestriction l X) (diagonalRealizationPull l hX)
    (diagonalCompletedRestriction l X') ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX))
    p.restrictionX.F d.geometry.pull p'.restrictionX.F
    d.completedOrdinary d.varyingOrdinary p.LX p'.LX d.limitMate
    r.completedLine.hom d.line.iso.hom
    p.coefficientsX.lineProjection p'.coefficientsX.lineProjection
    (by
      simpa only [Functor.mapCone, NatTrans.ext_iff,
        NatTrans.comp_app, Functor.compConstIso, NatIso.ofComponents_hom_app,
        Iso.refl_hom, Functor.whiskerRight_app, Functor.const_map_app,
        Category.id_comp] using hπ.symm)
    d.cone
  simpa only [LocalChernPullbackData.completedSquare,
    LocalChernPullbackData.comparison, Coefficients.lineMap,
    diagonalRealizationPullSingle, line_derivedIso_eq, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom,
    diagonalCompletedUnderlying, completedUnit, completedLine, SpTowerClasses.unit,
    SpTowerClasses.line, single_tower_eq] using ht

private theorem shift_endpoint
    {A B C D E E' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category E']
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift D ℤ] [HasShift E ℤ] [HasShift E' ℤ]
    (H : A ⥤ B) (F : A ⥤ C) (F' : B ⥤ D) (P : C ⥤ D)
    (J : E ⥤ C) (G : E ⥤ E') (J' : E' ⥤ D)
    [H.CommShift ℤ] [F.CommShift ℤ] [F'.CommShift ℤ] [P.CommShift ℤ]
    [J.CommShift ℤ] [G.CommShift ℤ] [J'.CommShift ℤ]
    (T : F ⋙ P ≅ H ⋙ F') (M : J ⋙ P ⟶ G ⋙ J')
    [NatTrans.CommShift T.hom ℤ] [NatTrans.CommShift M ℤ]
    {U : A} {U' : B} {V : E} {V' : E'}
    (cu : H.obj U ⟶ U') (a : F.obj U ⟶ J.obj V)
    (a' : F'.obj U' ⟶ J'.obj V') (q : G.obj V ⟶ V')
    (hu : T.inv.app U ≫ P.map a ≫ M.app V ≫ J'.map q = F'.map cu ≫ a') (j : ℤ) :
    T.inv.app (U⟦j⟧) ≫ P.map (shiftedComparison F J a j) ≫ M.app (V⟦j⟧) ≫
      J'.map ((G.commShiftIso j).hom.app V ≫ q⟦j⟧') =
    F'.map ((H.commShiftIso j).hom.app U ≫ cu⟦j⟧') ≫
      shiftedComparison F' J' a' j := by
  rw [NatTrans.app_shift T.inv, NatTrans.app_shift M]
  unfold shiftedComparison
  simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Iso.inv_hom_id_app_assoc, Category.comp_id]
  rw [← P.commShiftIso_inv_naturality_assoc a j]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [J'.map_id, Category.id_comp]
  rw [← J'.commShiftIso_inv_naturality q j]
  simp only [← (shiftFunctor D j).map_comp_assoc]
  rw [hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [F'.commShiftIso_hom_naturality_assoc cu j]

private theorem exactSquare_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits U]
    [CategoryTheory.Limits.PreservesFiniteColimits U]
    [CategoryTheory.Limits.PreservesFiniteLimits P]
    [CategoryTheory.Limits.PreservesFiniteColimits P]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    [CategoryTheory.Limits.PreservesFiniteLimits V]
    [CategoryTheory.Limits.PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V) :
    NatTrans.CommShift (Functor.mapDerivedCategorySquareIso s).hom ℤ := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance
private theorem comparison_commShift
    {A A' B C D E : Type*}
    [Category A] [Category A'] [Category B] [Category C] [Category D] [Category E]
    [HasShift A ℤ] [HasShift A' ℤ] [HasShift B ℤ]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (V : A ⥤ B) (R : B ⥤ C) (P : C ⥤ D) (W : B ⥤ E)
    (R' : E ⥤ D) (G : A ⥤ A') (V' : A' ⥤ E)
    [V.CommShift ℤ] [R.CommShift ℤ] [P.CommShift ℤ] [W.CommShift ℤ]
    [R'.CommShift ℤ] [G.CommShift ℤ] [V'.CommShift ℤ]
    (μ : R ⋙ P ⟶ W ⋙ R') (ν : V ⋙ W ≅ G ⋙ V')
    [NatTrans.CommShift μ ℤ] [NatTrans.CommShift ν.hom ℤ] :
    NatTrans.CommShift
      ((Functor.associator V R P).hom ≫ Functor.whiskerLeft V μ ≫
        (Functor.associator V W R').inv ≫ Functor.whiskerRight ν.hom R' ≫
        (Functor.associator G V' R').hom) ℤ := by
  infer_instance

-- Instantiate the exact cone diagram on the normalized completed endpoints.
/-- The normalized positive-root cone is preserved, including the canonical shift.

Source: latest blueprint, diagonal coefficient changes (3).
(blueprint: lem-diagonal-local-chern-root-pullback).

Proof: use the full cone equation in the pullback data for the completed root module and
its lineProjection. Transpose the ordinary scalar comparison using completedMate and
varyingMate. The normalized right comparisons are the identity on underlying sections.
At each root projection the completed line endpoint is therefore the actual root
inverse-image map, by completedLine_normalization. On a root tensored with a coefficient,
LinePullback.normalization gives the same root inverse image with the pulled coefficient.
The line_tensor equation identifies every restricted line section with a root tensored
with one. Its finite line evaluation is the specified tensor. The normalized pullback
therefore sends it to the pulled root; injectivity of the finite evaluation and scalar
restriction identifies the line sections. Together with line_projection, sheaf/module
and tower extensionality give equality of entire cones.
Substitute in the cone equation, and use exact-derived composition and single comparison
naturality. This gives the unshifted line equation. Shift it by two. The canonical exact
scalar squares, the whole-tower comparison and the derived tower functors commute with
shifts. Naturality of those shift isomorphisms gives exactly the displayed equation,
with the positive Kummer root comparison and without a change of connecting-map sign.
No faithfulness of derived finite evaluation is used. -/
theorem diagonalLocalChern_root_pullback (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (hunit : IsUnit (l : Γ(X, ⊤))) (hunit' : IsUnit (l : Γ(X', ⊤)))
    (eX : CompletedRealization l X) (eX' : CompletedRealization l X')
    (r : DiagonalRealizationPullback l hX eX' eX)
    (d : LocalChernPullbackData l hX p p') :
    (d.completedSquare l).inv.app ((completedLine l X)⟦(2 : ℤ)⟧) ≫
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory.map
        (shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2) ≫
      (d.comparison l).app ((SpTowerClasses.line l (ULift.{u} (Padic l)) p.chernX)⟦(2 : ℤ)⟧) ≫
      p'.LX.R.map (p'.restrictionX.F.mapDerivedCategory.map
        (((SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry).commShiftIso
          (2 : ℤ)).hom.app (SpTowerClasses.line l (ULift.{u} (Padic l)) p.chernX) ≫
          ((d.line.derivedIso l (ULift.{u} (Padic l))).hom)⟦(2 : ℤ)⟧')) =
    (diagonalCompletedUnderlying l X').map
      (diagonalRealizationPullShift l hX r.completedLine 2).hom ≫
      shiftedComparison (diagonalCompletedUnderlying l X')
        (p'.restrictionX.F.mapDerivedCategory ⋙ p'.LX.R)
        (p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX) 2 := by
  let := d.geometry.pullAdditive
  let := d.geometry.pullLimits
  let := d.geometry.pullColimits
  let := p.restrictionX.additive
  let := p.restrictionX.limits
  let := p.restrictionX.colimits
  let := p'.restrictionX.additive
  let := p'.restrictionX.limits
  let := p'.restrictionX.colimits
  let : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)) := d.towerLimits
  let : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)) := d.towerColimits
  let H := (diagonalRealizationPull l hX).mapDerivedCategory
  let F := diagonalCompletedUnderlying l X
  let F' := diagonalCompletedUnderlying l X'
  let P := ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory
  let J := p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R
  let J' := p'.restrictionX.F.mapDerivedCategory ⋙ p'.LX.R
  let G := SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry
  let T := d.completedSquare l
  let M := d.comparison l
  let : NatTrans.CommShift T.hom ℤ := by
    dsimp only [T, LocalChernPullbackData.completedSquare, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let : NatTrans.CommShift d.limitMate ℤ := d.mateShifts
  let : NatTrans.CommShift
      (Functor.mapDerivedCategorySquareIso d.varyingOrdinary).hom ℤ :=
    exactSquare_commShift p.restrictionX.F _ d.geometry.pull p'.restrictionX.F
      d.varyingOrdinary
  let : NatTrans.CommShift M ℤ := by
    dsimp only [M, LocalChernPullbackData.comparison]
    exact comparison_commShift p.restrictionX.F.mapDerivedCategory p.LX.R
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory p'.LX.R
      (SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry)
      p'.restrictionX.F.mapDerivedCategory d.limitMate
      (Functor.mapDerivedCategorySquareIso d.varyingOrdinary)
  have hu := horizontal_root_unshifted l hX p p' hunit hunit' eX eX' r d
  have hs := shift_endpoint
    (E := DerivedCategory (Systems X (Arings l (ULift.{u} (Padic l)) X)))
    (E' := DerivedCategory (Systems X' (Arings l (ULift.{u} (Padic l)) X')))
    H F F' P J G J' T M
    (diagonalRealizationPullSingle l hX r.completedLine).hom
    (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX)
    (p'.coefficientsX.lineMap l (ULift.{u} (Padic l)) p'.LX)
    (d.line.derivedIso l (ULift.{u} (Padic l))).hom hu 2
  simpa only [H, F, F', P, J, J', G, T, M, Functor.comp_map,
    diagonalRealizationPullShift, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, single_tower_eq, shift_tower_eq] using hs

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
