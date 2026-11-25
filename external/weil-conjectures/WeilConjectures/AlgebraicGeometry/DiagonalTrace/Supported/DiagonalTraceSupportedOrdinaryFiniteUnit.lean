/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedSupportedUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import WeilConjectures.CategoryTheory.SixFunctors.CompletedCoefficientLocalIntegers
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRingComparison
import WeilConjectures.AlgebraicGeometry.Supported.SupportedIntegralGeneratorSections

/-! # The ordinary supported finite unit, determined by its integral generator -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] diagonalCompletedCoefficientMap
  diagonalCompletedGenerator
  cartierProIntegralGenerator completedSupportedUnit SpTowerClasses.lineModule

private theorem completedMap_ext (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (n : ℕ) (Q : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (f g : (SheafOfModules.toSheaf
        (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj
      (SheafOfModules.unit
        (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ⟶ Q)
    (hQ : ∀ (V : X.ProEtᵒᵖ) (y : Q.obj.obj V), l ^ (n + 1) • y = 0)
    (h1 : ∀ V : X.ProEtᵒᵖ,
      f.hom.app V (1 : (Scheme.purTwistZlCompletion X l).obj.obj V) =
        g.hom.app V (1 : (Scheme.purTwistZlCompletion X l).obj.obj V)) : f = g := by
  obtain ⟨e, _, _⟩ := DiagonalCoefficients.completedCoefficientRingComparison_existsUnique l X
  let S := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
  let J := Scheme.ProEt.topology X
  let F := sheafCompose J (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let f' := F.map e.hom ≫ f
  let g' := F.map e.hom ≫ g
  have h1' (V : X.ProEtᵒᵖ) :
      f'.hom.app V (1 : S.obj.obj V) = g'.hom.app V (1 : S.obj.obj V) := by
    change f.hom.app V (e.hom.hom.app V 1) = g.hom.app V (e.hom.hom.app V 1)
    simpa only [map_one] using h1 V
  have hfg : f' = g' := by
    ext V x
    let sieve := integerApproximationSieve S (l ^ (n + 1)) x
    apply Q.isSeparated V.unop sieve
      (DiagonalCoefficients.completedCoefficient_localIntegers l X n V x)
    rintro W i ⟨a, b, hb⟩
    rw [← NatTrans.naturality_apply f'.hom i.op x,
      ← NatTrans.naturality_apply g'.hom i.op x]
    change f'.hom.app (op W) (S.obj.map i.op x) =
      g'.hom.app (op W) (S.obj.map i.op x)
    rw [hb, map_add, map_add, map_nsmul, map_nsmul, hQ, hQ, add_zero, add_zero]
    have hc : (a : S.obj.obj (op W)) = a • (1 : S.obj.obj (op W)) :=
      (zsmul_one a).symm
    rw [hc, map_zsmul, map_zsmul, h1']
  apply (cancel_epi (F.map e.hom)).mp
  exact hfg

/-- The ordinary completed-to-finite supported unit is fixed by its integral generator.
There are no Ext classes, derived presentations, roots, or derived limits in this statement.

Source: blueprint latest, diagonal trace proof (2), source projection, together with
its diagonal-limit source normalization (3).
(blueprint: lem-sfb-diagonal-trace-supported-ordinary-finite-unit).

Proof: the finite supported constant is killed by l^(n+1). The hypothesis on f says
that its value on the integral supported generator is the canonical residue generator.
The completed supported unit sends one to one on the pulled-back diagonal chart.
Consequently the left composite sends every local coefficient one to the image of one
under the constant-to-supported finite unit. For the right composite,
k.coefficient_projection identifies the coefficient cone component with the actual
completed ring projection. This unital ring map sends one to one; ha measures
normalization through coefficientForget and identifies its image under a with
the sheafification of residue one. This condition remains meaningful for every
isomorphic presentation of the source coefficient object. The finite unit
again sends this to the same supported residue generator. Both sides therefore agree
on one over every object. To extend this equality to an arbitrary completed section,
reduce modulo l^(n+1). The completed coefficient sheaf has the actual constant finite
ring as this quotient: equivalently every section is locally an integer plus
l^(n+1) times a section. Additivity makes the two maps agree on the integer part, and
the remaining part vanishes in the finite supported target. Sheaf separatedness gives
the equality globally. Positive exponent n+1 includes n=0, and the sheaf axiom handles
the empty object. -/
theorem diagonalTrace_supportedOrdinaryFiniteUnit
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (n : ℕ)
    (f : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ⟶
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))))
    (hf : HEq (diagonalCompletedGenerator l Y ≫
        (diagonalForget l (diagonalSurface Y)).map f)
      (cartierProIntegralGenerator (diagonalResidue.{u} l n) (diagonalImmersion Y)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (a : (r.F.obj (SpTowerClasses.coefficient (diagonalSurface Y)
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj (op n) ≅
        (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y)))
    (ha : ∀ (U : (diagonalSurface Y).ProEtᵒᵖ)
        (x : ((r.F.obj (SpTowerClasses.coefficient (diagonalSurface Y)
          (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj
            (op n)).obj.obj U),
      (k.coefficientForget.hom.app (op n)).hom.app U x =
        (1 : (Scheme.purTwistFiniteRing (diagonalSurface Y) l n).obj.obj U) →
      HEq (a.hom.hom.app U x)
        ((toSheafify (Scheme.ProEt.topology (diagonalSurface Y))
          ((Functor.const (diagonalSurface Y).ProEtᵒᵖ).obj
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
              (1 : diagonalResidue.{u} l n))) :
    (diagonalCompletedRestriction l (diagonalSurface Y)).map (completedSupportedUnit l Y) ≫
        f =
      k.coefficientProjection.app (op n) ≫ a.hom ≫
        (diagonalFiniteToPadic l n (diagonalSurface Y)).map
          (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
            (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))) := by
  have : (diagonalForget l (diagonalSurface Y)).Faithful := by
    unfold diagonalForget
    infer_instance
  apply (diagonalForget l (diagonalSurface Y)).map_injective
  apply completedMap_ext l (diagonalSurface Y) n
  · intro V y
    have h (z : (((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))).obj.obj V)) :
        l ^ (n + 1) • z = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (diagonalResidue.{u} l n),
        cartierResidue_cast l (n + 1), zero_smul]
    unfold diagonalForget diagonalFiniteToPadic at y ⊢
    exact h y
  · intro U
    let W := diagonalSurface Y
    let Z := ProjectiveLine Y
    let i := diagonalImmersion Y
    let V := op ((Scheme.proEtaleBaseChange i).obj U.unop)
    let eta := toSheafify (Scheme.ProEt.topology Z)
      ((Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    have hg : HEq ((diagonalCompletedGenerator l Y).hom.app U
      (eta.app V (ULift.up (1 : ℤ))))
      ((1 : ℤ) • (1 : (Scheme.purTwistZlCompletion Z l).obj.obj V)) := by
      simpa only [diagonalCompletedGenerator] using
        (diagonalCompletedGenerator_existsUnique l Y).exists.choose_spec U (1 : ℤ)
    have hg' : (diagonalCompletedGenerator l Y).hom.app U
        (eta.app V (ULift.up (1 : ℤ))) =
          (1 : (Scheme.purTwistZlCompletion Z l).obj.obj V) := by
      simpa only [one_zsmul] using eq_of_heq hg
    unfold diagonalForget diagonalFiniteToPadic at hf
    have hf' := congrArg (fun q ↦ q.hom.app U (eta.app V (ULift.up (1 : ℤ))))
      (eq_of_heq hf)
    change f.hom.app U ((diagonalCompletedGenerator l Y).hom.app U
      (eta.app V (ULift.up (1 : ℤ)))) =
        (cartierProIntegralGenerator (diagonalResidue.{u} l n) i).hom.app U
          (eta.app V (ULift.up (1 : ℤ))) at hf'
    rw [hg', supported_integral_generator_sections, Int.cast_one] at hf'
    let x : (((diagonalCompletedRestriction l W).obj
        (SheafOfModules.unit (Scheme.purTwistRing W
          (Scheme.purTwistZlCompletion W l)))).obj.obj U) :=
      (1 : (Scheme.purTwistZlCompletion W l).obj.obj U)
    have hu : (((diagonalCompletedRestriction l W).map
        (completedSupportedUnit l Y)).hom.app U) x =
          (1 : (Scheme.purTwistZlCompletion Z l).obj.obj V) := by
      change (completedSupportedUnit l Y).val.app U
        (1 : (Scheme.purTwistZlCompletion W l).obj.obj U) = _
      simp only [completedSupportedUnit, id_eq]
      erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
      exact map_one (M := (Scheme.purTwistZlCompletion W l).obj.obj U)
        (N := (Scheme.purTwistZlCompletion Z l).obj.obj V) _
    have hp0 := k.coefficient_projection n U x
    have hp : (k.coefficientForget.hom.app (op n)).hom.app U
        ((k.coefficientProjection.app (op n)).hom.app U x) =
        (1 : (Scheme.purTwistFiniteRing W l n).obj.obj U) := by
      rw [hp0]
      exact map_one (M := (Scheme.purTwistZlCompletion W l).obj.obj U)
        (N := (Scheme.purTwistFiniteRing W l n).obj.obj U) _
    have ha' := eq_of_heq (ha U _ hp)
    let A := ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)
    let etaW := toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj A)
    let etaZ := toSheafify (Scheme.ProEt.topology Z)
      ((Functor.const Z.ProEtᵒᵖ).obj A)
    have hc : etaW ≫ (Scheme.proEtaleConstantDirectImageMap i
        (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) A).hom =
        Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op etaZ := by
      exact ((sheafificationAdjunction (Scheme.ProEt.topology W)
        (ModuleCat.{u + 1} (diagonalResidue.{u} l n))).homEquiv _ _).apply_symm_apply _
    have hc' := congrArg (fun q ↦ q.app U (1 : diagonalResidue.{u} l n)) hc
    unfold diagonalForget diagonalFiniteToPadic
    change f.hom.app U
      ((((diagonalCompletedRestriction l W).map (completedSupportedUnit l Y)).hom.app U)
        (1 : (Scheme.purTwistZlCompletion W l).obj.obj U)) =
      (Scheme.proEtaleConstantDirectImageMap i
        (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) A).hom.app U
          (a.hom.hom.app U ((k.coefficientProjection.app (op n)).hom.app U
            x))
    rw [hu, hf', ha']
    exact hc'.symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
