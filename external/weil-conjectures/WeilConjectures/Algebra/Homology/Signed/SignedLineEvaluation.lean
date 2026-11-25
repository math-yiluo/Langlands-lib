/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair

/-! # Native evaluation of the existing signed line powers

Source: Stacks 03EO and 04TT; blueprint Proof (3), evaluation of signed powers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
attribute [local instance 2000] cochainModulesMonoidal

/-- Multiplication in degree zero and the actual internal Hom evaluation otherwise.
Source: Stacks 03EO and 04TT (blueprint: lem-pur-signed-line-native-evaluation). -/
def signedLinePairing (L : LineEvaluation.Modules.{uC, vC, r} R) (m : ℤ) (U : Cᵒᵖ) :
    (signedLinePower.{uC, vC, r} L m).val.obj U →
      (signedLinePower.{uC, vC, r} L (-m)).val.obj U → R.obj.obj U :=
  match m with
  | .ofNat 0 => fun a b ↦ (@id (R.obj.obj U) a) * (@id (R.obj.obj U) b)
  | .ofNat (_n + 1) => fun a b ↦ b.app (op (Over.mk (𝟙 U.unop))) a
  | .negSucc _n => fun a b ↦ a.app (op (Over.mk (𝟙 U.unop))) b

omit [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})] in
private theorem dualEvaluation (P : LineEvaluation.Modules.{uC, vC, r} R)
    [P.IsFiniteLocallyFreeOfRank 1] :
    ∃ e : P ⊗ LineEvaluation.unitDual.{uC, vC, r}
        (R) P ≅ unit
        ((sheafCompose (J)
          (forget₂ CommRingCat RingCat)).obj
            (R)),
      ∀ U x phi, e.hom.val.app U
        (LineEvaluation.pureTensor.{uC, vC, r}
          (R) _ _ U x phi) =
        phi.app (op (Over.mk (𝟙 U.unop))) x := by
  classical
  let Rm := (sheafCompose (J)
    (forget₂ CommRingCat RingCat)).obj R
  have hcover : ∀ U : C, ∃ s : Sieve U,
      s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit (Rm.over V)) := by
    obtain ⟨I, V, hV, h⟩ :=
      (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := P) (r := 1)).mp inferInstance
    intro U
    refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
    rintro Z f ⟨i, ⟨g⟩⟩
    let e : P.over (V i) ≅ unit (Rm.over (V i)) :=
      (h i).some ≪≫ freeUniqueIso (ULift (Fin 1))
    exact ⟨((overFunctorMap Rm g).app P).symm ≪≫
      (overMap Rm g).mapIso e ≪≫ overMapUnitIso (R := Rm) g⟩
  have := LineEvaluation.evaluation_isIso.{uC, vC, r} R P hcover
  exact ⟨asIso (LineEvaluation.evaluation.{uC, vC, r} R P),
    LineEvaluation.evaluation_pure.{uC, vC, r} R P⟩

/-- The specified signed-power evaluation comes from an actual sheaf isomorphism.
Source: Stacks 03EO and 04TT
(blueprint: lem-pur-signed-line-native-evaluation).
Proof: on a trivializing covering, each positive tensor power is the unit. Hence
it is a line. Its Hom evaluation is invertible by local rank-one evaluation and
gluing. Use this evaluation in positive degrees, precompose it with symmetry in
negative degrees, and use multiplication in degree zero. The pure-section formulas
for evaluation, symmetry and the unitor give exactly the stated pairing. -/
theorem signedLineEvaluation_exists (L : LineEvaluation.Modules.{uC, vC, r} R)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    ∃ e : signedLinePower.{uC, vC, r} L m ⊗ signedLinePower.{uC, vC, r} L (-m) ≅ unit
        ((sheafCompose (J)
          (forget₂ CommRingCat RingCat)).obj
            (R)),
      ∀ U a b, e.hom.val.app U
        (LineEvaluation.pureTensor.{uC, vC, r}
          (R) _ _ U a b) =
        signedLinePairing.{uC, vC, r} R L m U a b := by
  have hr (n : ℕ) :
      (signedLinePower.{uC, vC, r} L (Int.ofNat (n + 1))).IsFiniteLocallyFreeOfRank 1 := by
    change (scalarTensorPower R L (n + 1)).IsFiniteLocallyFreeOfRank 1
    apply (isInvertible_iff_isFiniteLocallyFreeOfRank_one
      (scalarTensorPower R L (n + 1))).mp
    obtain ⟨I, V, hV, h⟩ :=
      (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := L) (r := 1)).mp inferInstance
    apply isInvertible_of_forall_over_unit (M := scalarTensorPower R L (n + 1)) V hV
    intro i
    exact power_over_unit.{uC, vC, max uC vC r} L (V i)
      ((h i).some ≪≫ freeUniqueIso (ULift (Fin 1))) (n + 1)
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      refine ⟨ρ_ _, ?_⟩
      intro U a b
      change R.obj.obj U at a b
      have h := LineEvaluation.pure_right_unitor.{uC, vC, r} R
        (signedLinePower.{uC, vC, r} L 0) U a b
      have h' : (b : R.obj.obj U) * (a : R.obj.obj U) =
          (a : R.obj.obj U) * (b : R.obj.obj U) := mul_comm _ _
      exact h.trans h'
    | succ n =>
      have := hr n
      obtain ⟨e, he⟩ := dualEvaluation.{uC, vC, r} R
        (signedLinePower.{uC, vC, r} L (Int.ofNat (n + 1)))
      exact ⟨e, he⟩
  | negSucc n =>
    have := hr n
    obtain ⟨e, he⟩ := dualEvaluation.{uC, vC, r} R
        (signedLinePower.{uC, vC, r} L (Int.ofNat (n + 1)))
    refine ⟨(β_ _ _) ≪≫ e, ?_⟩
    intro U a b
    have h := LineEvaluation.pure_braiding.{uC, vC, r} R
      (LineEvaluation.unitDual.{uC, vC, r} R
        (signedLinePower.{uC, vC, r} L (.ofNat (n + 1))))
      (signedLinePower.{uC, vC, r} L (.ofNat (n + 1))) U a b
    exact (congrArg (e.hom.val.app U) h).trans (he U b a)

end SheafOfModules
