/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceNormalizedRootIso
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceResidueRestriction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientIdentification
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceLineIdentification

/-! # Scalar restriction and coefficient cones at one site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private def liftRestrictionCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶
      r.F.obj M ⋙ diagonalForget l T) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ r.F.obj M where
  app n := liftToRestriction l T r M n.unop Q (π.app n)
  naturality a b g := by
    ext U x
    exact congrArg (fun k ↦ k.hom.app U x) (π.naturality g)

private def transportRestrictionCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T) (H : ℕᵒᵖ ⥤ DiagonalAb T)
    (e : r.F.obj M ⋙ diagonalForget l T ≅ H)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶ H) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ r.F.obj M :=
  liftRestrictionCone l T r M Q (π ≫ e.inv)

private theorem transportRestrictionCone_section (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T))
    (Q : DiagonalMod l T) (H : ℕᵒᵖ ⥤ DiagonalAb T)
    (e : r.F.obj M ⋙ diagonalForget l T ≅ H)
    (π : (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj Q) ⟶ H)
    (n : ℕ) (U : T.ProEtᵒᵖ) (x : Q.obj.obj U) :
    (e.hom.app (op n)).hom.app U
      (((transportRestrictionCone l T r M Q H e π).app (op n)).hom.app U x) =
        (π.app (op n)).hom.app U x := by
  have h := congrArg (fun k ↦ k.hom.app U ((π.app (op n)).hom.app U x))
    (NatTrans.congr_app e.inv_hom_id (op n))
  exact h

private def coefficientCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj
      ((diagonalCompletedRestriction l T).obj
        (SheafOfModules.unit (Scheme.purTwistRing T (Scheme.purTwistZlCompletion T l))))) ⟶
    Scheme.purTwistZlTower T l ⋙
      sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  ((sheafCompose (Scheme.ProEt.topology T)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapCone
        (limit.cone (Scheme.purTwistZlTower T l))).π

private def rootCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj ((diagonalForget l T).obj
      ((diagonalCompletedRestriction l T).obj (Scheme.purTwistZlModule T l))) ⟶
      roots l T := (limit.cone (roots l T)).π

-- The finite constructions do not use the derived Chern normalization.
set_option linter.unusedVariables false in
/-- The exact finite-coefficient restriction and its two normalized cones at one site.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
coefficient restriction and its coefficient-unit and Tate-line identifications.
(blueprint: lem-sfb-diagonal-trace-coefficient-restriction).

Proof: restrict each level action along the constant-section map from Z_l to
O_(ULift Q_l)/l^(n+1). Retain the additive section groups, all vertical restrictions,
all horizontal transitions, and all maps. The quotient maps commute with residues,
so these are Z_l-linear and define a functor on strict systems. The residue of z acts
as its representative natural number; this proves the prescribed scalar equation.
Kernels are sectionwise, and additive sheafification computes cokernels, so this
restriction preserves finite limits and colimits and is additive.
Identify the valuation-one subring of ULift Q_l with Z_l by the lifted identity.
Its quotients by l^(n+1) identify with Z/l^(n+1), compatibly with all quotient maps.
The resulting isomorphism of constant ring towers gives coefficientForget and sends
one to one. Extension along the same ring isomorphism has the tensor unitor as its
counit: on a pure tensor with scalar one it sends x tensor one to x. Compose this
with c.rootForget to obtain lineForget, with the required line_tensor equation.
Transport the actual completed ring projections through coefficientForget inverse,
and the actual root-limit projections through lineForget inverse. These maps are
Z_l-linear, commute with the quotient transitions, and give the two cones.
Cancelling the corresponding inverse isomorphisms proves coefficient_projection
and line_projection. These constructions include the first positive quotient and
empty sites; they impose no condition on a scheme morphism or on direct image. -/
theorem exists_diagonalTraceCoefficientRestriction (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (hc : c.Normalized l (ULift.{u} (Padic l))) :
    ∃ r : Restriction l (ULift.{u} (Padic l)) T,
      Nonempty (Coefficients l (ULift.{u} (Padic l)) T c r) := by
  obtain ⟨r⟩ := exists_diagonalTraceResidueRestriction l T
  let e := diagonalTraceCoefficientIdentification l T r
  let f := diagonalTraceLineIdentification l T c r
  refine ⟨r, ⟨{
    coefficientForget := e
    coefficient_one := diagonalTraceCoefficientIdentification_hom_app_hom_app_eq_one l T r
    lineForget := f
    line_tensor := diagonalTraceLineIdentification_hom_app_hom_app l T c r
    coefficientProjection := transportRestrictionCone l T r _ _ _ e (coefficientCone l T)
    coefficient_projection := ?_
    lineProjection := transportRestrictionCone l T r _ _ _ f (rootCone l T)
    line_projection := ?_ }⟩⟩
  · intro n U x
    exact transportRestrictionCone_section l T r _ _ _ e (coefficientCone l T) n U x
  · intro n U x
    exact transportRestrictionCone_section l T r _ _ _ f (rootCone l T) n U x

end AlgebraicGeometry.ProEtale.DiagonalTrace
