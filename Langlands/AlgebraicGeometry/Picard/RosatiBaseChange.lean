import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AlgebraicGeometry.Picard.DualRationalBaseChange
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AbelianScheme.PrimeTraceBaseChange

/-! # Actual Rosati conjugation and trace form under base change -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Rosati

variable (P : Prerequisites.{u}) {S S' : Scheme.{u}} (b : S' ⟶ S)
  {A : AbelianScheme S} (W : DualData A) (W' : DualData ((baseChange b).obj A))

/-- The published canonical comparison identifies the pullback of the actual dual
with the actual dual constructed from the chosen data on the pullback. -/
def DualData.baseChangeIso : (baseChange b).obj (W.dual P) ≅ W'.dual P :=
  dualAbelianBaseChangeIso P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality dualAbelianBaseChange b A
    W.hasDual W.geometry W.inversePoincare W.evaluation
    W'.hasDual W'.geometry W'.inversePoincare W'.evaluation

/-- Actual pullback of a map to the actual dual, with its canonical target comparison. -/
def DualData.baseChangeMap (lam : A ⟶ W.dual P) :
    (baseChange b).obj A ⟶ W'.dual P :=
  (baseChange b).map lam ≫ (DualData.baseChangeIso P b W W').hom

local notation "A'" => Functor.obj (baseChange b) A
local notation "D" => W.dual P
local notation "D'" => W'.dual P
local notation "E" => DualData.baseChangeIso P b W W'

/-- Rational dualization satisfies the actual canonical comparison square. -/
theorem dual0_baseChange (hadd : W.Additivity P) (hadd' : W'.Additivity P)
    (a : End0 A) :
    comp0 ((baseChange b).obj D) ((baseChange b).obj D) D'
      (rationalBaseChangeHom b (W.dual0 P hadd a).asHom) (homToHom0 (E).hom) =
    comp0 ((baseChange b).obj D) D' D'
      (homToHom0 (E).hom)
      (W'.dual0 P hadd' (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom))).asHom :=
  dualHom0_baseChange_of_naturality P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality dualAbelianBaseChange b A
    W.hasDual W.geometry W.inversePoincare W.evaluation
    W'.hasDual W'.geometry W'.inversePoincare W'.evaluation A
    W.hasDual W.geometry W.inversePoincare W.evaluation
    W'.hasDual W'.geometry W'.inversePoincare W'.evaluation
    hadd hadd' dualAbelianBaseChangeNaturality a.asHom

variable (hadd : W.Additivity P) (hadd' : W'.Additivity P)
  (lam : A ⟶ W.dual P)

local notation "lam'" => DualData.baseChangeMap P b W W' lam

/-- The existing rational inverse remains available for the actual transported map. -/
theorem hasRationalInverse_baseChange [HasRationalInverse P W lam] :
    HasRationalInverse P W' lam' := by
  change IsIso ((rationalization S').map ((baseChange b).map lam ≫ (E).hom))
  rw [Functor.map_comp]
  have : IsIso ((rationalization S').map ((baseChange b).map lam)) := by
    have heq : (rationalBaseChange b).map ((rationalization S).map lam) =
        (rationalization S').map ((baseChange b).map lam) :=
      rationalBaseChangeHom_ofHom b lam
    rw [← heq]
    infer_instance
  infer_instance

/-- The actual rationalization of the transported map factors through the canonical comparison. -/
theorem homToHom0_baseChangeMap :
    homToHom0 lam' =
      comp0 A' ((baseChange b).obj D) D'
        (rationalBaseChangeHom b (homToHom0 lam)) (homToHom0 (E).hom) := by
  simp only [homToHom0_apply, rationalBaseChangeHom_tmul, comp0_tmul, one_mul]
  rfl

variable [hinv : HasRationalInverse P W lam]
  [hinv' : HasRationalInverse P W' (DualData.baseChangeMap P b W W' lam)]

/-- Actual Rosati conjugation commutes with the actual rational Hom pullback. -/
theorem involution_baseChange (a : End0 A) :
    @involution S' A' P W' hadd' lam' hinv'
        (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom)) =
      CategoryTheory.End.of (rationalBaseChangeHom b (involution P W hadd lam a).asHom) := by
  have hsource :
      comp0 A A D (involution P W hadd lam a).asHom (homToHom0 lam) =
        comp0 A D D (homToHom0 lam) (W.dual0 P hadd a).asHom := by
    rw [involution_apply, comp0_assoc, inverse_comp_polarization, comp0_id0]
  have hpull := congrArg (rationalBaseChangeHom b) hsource
  change rationalBaseChangeHom b (Langlands.Rationalization.comp A A D
      (involution P W hadd lam a).asHom (homToHom0 lam)) =
    rationalBaseChangeHom b (Langlands.Rationalization.comp A D D
      (homToHom0 lam) (W.dual0 P hadd a).asHom) at hpull
  simp only [rationalBaseChangeHom_comp] at hpull
  change comp0 A' A' ((baseChange b).obj D)
      (rationalBaseChangeHom b (involution P W hadd lam a).asHom)
      (rationalBaseChangeHom b (homToHom0 lam)) =
    comp0 A' ((baseChange b).obj D) ((baseChange b).obj D)
      (rationalBaseChangeHom b (homToHom0 lam))
      (rationalBaseChangeHom b (W.dual0 P hadd a).asHom) at hpull
  have htransport :
      comp0 A' A' D' (rationalBaseChangeHom b (involution P W hadd lam a).asHom)
          (homToHom0 lam') =
        comp0 A' D' D' (homToHom0 lam')
          (W'.dual0 P hadd'
            (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom))).asHom := by
    rw [homToHom0_baseChangeMap, ← comp0_assoc, hpull, comp0_assoc,
      dual0_baseChange, ← comp0_assoc]
  have htarget :
      comp0 A' A' D'
          (@involution S' A' P W' hadd' lam' hinv'
            (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom))).asHom
          (homToHom0 lam') =
        comp0 A' D' D' (homToHom0 lam')
          (W'.dual0 P hadd'
            (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom))).asHom := by
    rw [involution_apply, comp0_assoc, inverse_comp_polarization, comp0_id0]
  have h := congrArg
    (fun z => comp0 A' D' A' z (polarizationInverse P W' lam'))
    (htarget.trans htransport.symm)
  apply CategoryTheory.End.ext
  simpa only [comp0_assoc, polarization_comp_inverse, comp0_id0] using h

end Langlands.AbelianScheme.Rosati

namespace Langlands.AbelianScheme.Rosati

variable (hcomparison : GeometricEndomorphismTraceComparisonStatement.{u})
  (P : Prerequisites.{u})
  {k K : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  [Field K] [IsAlgClosed K] [CharZero K]
  (b : Spec (.of K) ⟶ Spec (.of k)) {A : AbelianScheme (Spec (.of k))}
  (W : DualData A) (W' : DualData ((baseChange b).obj A))
  (hadd : W.Additivity P) (hadd' : W'.Additivity P) (lam : A ⟶ W.dual P)
  [hinv : HasRationalInverse P W lam]
  [hinv' : HasRationalInverse P W' (DualData.baseChangeMap P b W W' lam)]

include hcomparison in
/-- Conditional on rational trace comparison, the full actual Rosati trace form
is preserved under geometric field base change. -/
theorem traceForm_baseChange_of_comparison (a c : End0 A) :
    @traceForm P K _ ((baseChange b).obj A) W' hadd'
      (DualData.baseChangeMap P b W W' lam) hinv'
      (CategoryTheory.End.of (rationalBaseChangeHom b a.asHom))
      (CategoryTheory.End.of (rationalBaseChangeHom b c.asHom)) =
      @traceForm P k _ A W hadd lam hinv a c := by
  rw [traceForm_apply, traceForm_apply, involution_baseChange]
  change geometricEndomorphismTrace ((baseChange b).obj A)
      ((rationalBaseChangeEnd b A) a * (rationalBaseChangeEnd b A)
        (involution P W hadd lam c)) = _
  rw [← map_mul]
  exact geometricEndomorphismTrace_baseChange_of_comparison hcomparison b A _

end Langlands.AbelianScheme.Rosati
