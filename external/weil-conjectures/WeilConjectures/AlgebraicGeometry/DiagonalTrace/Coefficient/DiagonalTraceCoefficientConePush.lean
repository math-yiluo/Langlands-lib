/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare

/-! # The ordinary coefficient cone and direct image

Source: diagonal tower trace proof (2), the unital coefficient square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem constantForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  GrothendieckTopology.instPreservesSheafification _ _
    (FD := fun A B : CommRingCat.{u + 1} ↦ A →+* B)
    (CD := fun A : CommRingCat.{u + 1} ↦ A)
    (FE := fun A B : AddCommGrpCat.{u + 1} ↦ A →+ B)
    (CE := fun A : AddCommGrpCat.{u + 1} ↦ A)

attribute [local instance] constantForgetSheafification

private theorem constant_additive_unit (T : Scheme.{u}) (A : CommRingCat.{u + 1})
    (U : T.ProEtᵒᵖ) (a : A) :
    (((constantCommuteCompose (Scheme.ProEt.topology T)
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app A).inv.hom.app U)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
              forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}).obj A))).app U a) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj A)).app U a := by
  let J := Scheme.ProEt.topology T
  let F := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let P := (Functor.const T.ProEtᵒᵖ).obj A
  have h : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (F.obj A)) ≫
      (sheafifyMap J (Functor.constComp T.ProEtᵒᵖ A F).inv ≫
        (sheafifyComposeIso J F P).hom) =
      (Functor.constComp T.ProEtᵒᵖ A F).inv ≫ Functor.whiskerRight (toSheafify J P) F := by
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
  exact ConcreteCategory.congr_hom (congr_app h U) a

private theorem constant_additive_ext (T : Scheme.{u}) (A : CommRingCat.{u + 1})
    (hA : ∀ x : A, ∃ k : ℤ, x = k • (1 : A))
    {F : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    (s t : (sheafCompose (Scheme.ProEt.topology T)
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj A) ⟶ F)
    (h : ∀ U : T.ProEtᵒᵖ,
      s.hom.app U (1 : ((constantSheaf (Scheme.ProEt.topology T)
        CommRingCat.{u + 1}).obj A).obj.obj U) =
      t.hom.app U (1 : ((constantSheaf (Scheme.ProEt.topology T)
        CommRingCat.{u + 1}).obj A).obj.obj U)) : s = t := by
  let J := Scheme.ProEt.topology T
  let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let e := (constantCommuteCompose J G).app A
  apply (cancel_epi e.inv).mp
  apply ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  ext U x
  change s.hom.app U (e.inv.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (G.obj A))).app U x)) =
    t.hom.app U (e.inv.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (G.obj A))).app U x))
  rw [constant_additive_unit]
  obtain ⟨k, hk⟩ := hA x
  rw [hk]
  simpa only [map_zsmul, map_one] using congrArg (k • ·) (h U)

private theorem additive_transport_apply
    {A B A' B' : AddCommGrpCat.{u + 1}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f.hom g.hom)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A'
  subst B'
  cases eq_of_heq hxy
  have h : f = g := AddCommGrpCat.hom_ext (eq_of_heq hfg)
  rw [h]

private theorem coefficient_inverse_one
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (a : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) (U : T.ProEtᵒᵖ) :
    HEq ((a.coefficientForget.inv.app (op n)).hom.app U
      (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U))
      (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
        (op (n, U.unop))) := by
  let N := SpTowerClasses.coefficient T
    (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T)
  let e := r.underlying N n U
  let y := (eqToHom e.symm)
    (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop)))
  have hy : HEq y (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop))) := eqToHom_heq e.symm _
  have h := congrArg (fun q ↦ q.hom.app U y) (a.coefficientForget.app (op n)).hom_inv_id
  change (a.coefficientForget.inv.app (op n)).hom.app U
    ((a.coefficientForget.hom.app (op n)).hom.app U y) = y at h
  rw [a.coefficient_one n U y hy] at h
  exact h.heq.trans hy

private theorem varying_coefficient_square
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let NX := SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
    let α := (p.model.geometry.ordinaryAdjunction.homEquiv _ _)
      p.model.coefficientPullback.iso.hom
    let G := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
    (diagonalForget l S).map
          ((p.restrictionS.F.map α ≫ p.varyingOrdinary.hom.app NX).app (op n)) ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          (p.coefficientsX.coefficientForget.hom.app (op n)) =
      p.coefficientsS.coefficientForget.hom.app (op n) ≫
        (sheafCompose (Scheme.ProEt.topology S) G).map
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) := by
  let E := ULift.{u} (Padic l)
  let NX := SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
  let NS := SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S)
  let α := (p.model.geometry.ordinaryAdjunction.homEquiv _ _)
    p.model.coefficientPullback.iso.hom
  dsimp only
  apply (cancel_epi (p.coefficientsS.coefficientForget.inv.app (op n))).mp
  apply constant_additive_ext S
    (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun x ↦ ⟨(ZMod.cast x.down : ℤ), by
      apply ULift.ext
      change x.down = (ZMod.cast x.down : ℤ) • (1 : ZMod (l ^ (n + 1)))
      simpa only [zsmul_eq_mul, mul_one]
        using (ZMod.intCast_zmod_cast x.down).symm⟩)
  intro U
  let y := (p.coefficientsS.coefficientForget.inv.app (op n)).hom.app U
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U)
  have hy := coefficient_inverse_one l S p.chernS p.restrictionS p.coefficientsS n U
  have hα := additive_transport_apply
    (p.restrictionS.underlying NS n U)
    (p.restrictionS.underlying (p.model.geometry.push.obj NX) n U)
    (AddCommGrpCat.ofHom
      ((((p.restrictionS.F.map α).app (op n)).hom.app U).hom.toAddMonoidHom))
    (AddCommGrpCat.ofHom ((α.val.app (op (n, U.unop))).hom.toAddMonoidHom))
    (p.restrictionS.morphisms α n U) y
    (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))) hy
  have hp := push_sections l E p.base p.model.geometry n NX U
    ((α.val.app (op (n, U.unop)))
      (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))))
  have hq := p.model.coefficientPullback.normalization n U
    (1 : (SpTowerShriek.B l E S n).obj.obj U)
    (1 : (SpTowerClasses.systemRing l E S).obj.obj (op (n, U.unop))) (HEq.rfl)
  have hβ : HEq
      (((p.varyingOrdinary.hom.app NX).app (op n)).hom.app U
        (((p.restrictionS.F.map α).app (op n)).hom.app U y))
      (1 : (SpTowerClasses.systemRing l E X).obj.obj
        (op (n, ((Scheme.proEtaleBaseChange f).op.obj U).unop))) := by
    exact (p.varying_sections NX n U _).trans
      (hα.trans (hp.symm.trans (hq.trans (heq_of_eq (map_one _)))))
  have hX := p.coefficientsX.coefficient_one n
    ((Scheme.proEtaleBaseChange f).op.obj U) _ hβ
  change (p.coefficientsX.coefficientForget.hom.app (op n)).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)
      (((p.varyingOrdinary.hom.app NX).app (op n)).hom.app U
        (((p.restrictionS.F.map α).app (op n)).hom.app U y)) =
    ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U)
        ((p.coefficientsS.coefficientForget.hom.app (op n)).hom.app U y)
  have hS := congrArg (fun q ↦ q.hom.app U
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U))
    (p.coefficientsS.coefficientForget.app (op n)).inv_hom_id
  change (p.coefficientsS.coefficientForget.hom.app (op n)).hom.app U y =
    (1 : (Scheme.purTwistFiniteRing S l n).obj.obj U) at hS
  rw [hS, map_one]
  exact hX

private theorem completed_projection_square
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (diagonalCompletedCoefficientMap l f)) ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (Scheme.purTwistZlProjection X l n) =
      Scheme.purTwistZlProjection S l n ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1))))) := by
  let a := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have h : diagonalCompletedCoefficientMap l f ≫ Scheme.purTwistZlProjection X l n =
      diagonalCompletedCoefficientComponent l f n := limit.lift_π _ (op n)
  have h' := congrArg (a.homEquiv _ _) h
  dsimp only [diagonalCompletedCoefficientComponent] at h'
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right] at h'
  exact h'.trans (by
    rw [show a.homEquiv _ _ (Scheme.proEtaleConstantInverseImageMap f
      CommRingCat.{u + 1} (CommRingCat.of.{u + 1}
        (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n + 1))))) from
      (a.homEquiv _ _).apply_symm_apply _])

private theorem completed_push_section
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S) (U : S.ProEtᵒᵖ)
    (x : (Scheme.purTwistZlCompletion S l).obj.obj U) :
    (((diagonalCompletedRestriction l S).map (completedPushUnit l f)).hom.app U) x =
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (diagonalCompletedCoefficientMap l f)).hom.app U) x := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The completed coefficient unit and the finite coefficient cones commute
with ordinary direct image. This is an equality of sheaf morphisms before any
right derivation or passage to a derived category.

Source: diagonal tower trace proof (2), ordinary coefficient square;
geometric classes proof (3), coefficient-pullback normalization.
(blueprint: lem-sfb-diagonal-trace-coefficient-cone-push).

Proof: apply ordinary limit extensionality. At level n, use limit.post_π
and the two cone lift equations. Forget the module structure, using the
faithful forgetful functor, and compose with coefficientsX.coefficientForget.
The coefficient_projection equations identify both cone components with the
actual ring-limit projections. The completed_sections and varying_sections
normalizations identify both direct-image comparisons with the identity on
sections. CoefficientPullback.normalization identifies the ordinary adjunct
with restriction of the finite constant coefficient ring. The unital
coefficient identifications are canonical: on a chart where a finite
constant-ring section is constant it is an integer multiple of one, so
additivity and coefficient_one determine them; the sheaf condition then
gives the equality for all sections. The ring-limit projections commute
with direct image because diagonalCompletedCoefficientMap is the lift of
the finite coefficient maps. This proves each level equation, hence the
ordinary limit equation. The argument includes n = 0, identity morphisms,
and empty charts; it does not assert faithfulness of derived evaluation. -/
theorem diagonalTrace_coefficient_cone_push
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    let E := ULift.{u} (Padic l)
    let H := p.restrictionX.F.obj (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))
    (diagonalCompletedRestriction l S).map (completedPushUnit l f) ≫
        p.completedOrdinary.hom.app
          (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).map
          (limit.lift H ⟨_, p.coefficientsX.coefficientProjection⟩) ≫
        p.limits.ordinary.hom.app H =
      limit.lift _ ⟨_, p.coefficientsS.coefficientProjection⟩ ≫
        (lim : DiagonalSystems l S ⥤ DiagonalMod l S).map
          (p.restrictionS.F.map
              ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
                p.model.coefficientPullback.iso.hom) ≫
            p.varyingOrdinary.hom.app
              (SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X))) := by
  let E := ULift.{u} (Padic l)
  let F := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let NX := SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
  let NS := SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S)
  let HX := p.restrictionX.F.obj NX
  let HS := p.restrictionS.F.obj NS
  let β : HS ⟶ HX ⋙ F := p.restrictionS.F.map
    ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
      p.model.coefficientPullback.iso.hom) ≫ p.varyingOrdinary.hom.app NX
  dsimp only
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, p.limits.ordinary_eq]
  erw [limit.post_π, ← F.map_comp, limit.lift_π, limMap_π, limit.lift_π_assoc]
  have : (diagonalForget l S).Faithful := by unfold diagonalForget; infer_instance
  apply (diagonalForget l S).map_injective
  apply (cancel_mono ((lowerStar AddCommGrpCat.{u + 1} f).map
    (p.coefficientsX.coefficientForget.hom.app n))).mp
  ext U x
  let x' := (((diagonalCompletedRestriction l S).map (completedPushUnit l f)).hom.app U) x
  let v := ((p.completedOrdinary.hom.app
    (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))).hom.app U) x'
  have hp := p.coefficientsX.coefficient_projection n.unop
    ((Scheme.proEtaleBaseChange f).op.obj U) v
  have hβ := congrArg (fun q ↦ q.hom.app U
    ((p.coefficientsS.coefficientProjection.app n).hom.app U x))
      (varying_coefficient_square l p n.unop)
  change (p.coefficientsX.coefficientForget.hom.app n).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)
      ((β.app n).hom.app U ((p.coefficientsS.coefficientProjection.app n).hom.app U x)) =
    ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))))).hom.app U)
      ((p.coefficientsS.coefficientForget.hom.app n).hom.app U
        ((p.coefficientsS.coefficientProjection.app n).hom.app U x)) at hβ
  rw [p.coefficientsS.coefficient_projection] at hβ
  have hc := congrArg (fun q ↦ q.hom.app U x)
    (completed_projection_square l f n.unop)
  have hv : v = (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      (diagonalCompletedCoefficientMap l f)).hom.app U) x :=
    eq_of_heq ((p.completed_sections _ U x').trans (heq_of_eq (completed_push_section l f U x)))
  change (p.coefficientsX.coefficientForget.hom.app n).hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)
      ((p.coefficientsX.coefficientProjection.app n).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U) v) = _
  rw [hp, hv]
  exact hc.trans hβ.symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
