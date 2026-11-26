import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.Representation.RankinSelberg.DiscreteSelfPairSupercuspidality
import Langlands.Representation.RankinSelberg.NormTwistedSelfPair
import Langlands.Representation.RankinSelberg.PoleOrderResidueDegree

/-! # Supercuspidality and the stabilizer count from a self-pair comparison -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis LocalFactor RankinSelberg
open _root_.Polynomial

universe u v uV

private theorem sum_normTwistStabilizer {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V)
    (chars : Finset (Fˣ →* ℂˣ)) (hchars : ∀ κ, κ ∈ chars ↔ IsNormTrivial E κ) :
    letI := Classical.decEq (Fˣ →* ℂˣ)
    letI (κ : chars) := Classical.propDecidable (Nonempty (π.Equiv (twist (κ.val.comp determinant) π)))
    (∑ κ : chars, if Nonempty (π.Equiv (twist (κ.val.comp determinant) π)) then 1 else 0) =
      Nat.card (normTwistStabilizer E π) := by
  classical
  let good (κ : chars) := Nonempty (π.Equiv (twist (κ.val.comp determinant) π))
  let selected := (Finset.univ : Finset chars).filter good
  let e : normTwistStabilizer E π ≃ selected := {
    toFun := fun κ => ⟨⟨κ.val, (hchars _).mpr κ.property.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, κ.property.2⟩⟩
    invFun := fun κ => ⟨κ.val.val, (hchars _).mp κ.val.property, (Finset.mem_filter.mp κ.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  change (∑ κ : chars, if good κ then (1 : ℕ) else 0) = selected.card
  have hsum : (∑ _κ ∈ selected, (1 : ℕ)) = selected.card := by simp
  rw [← hsum]
  dsimp only [selected]
  rw [Finset.sum_filter]

/-- A self-pair denominator comparison with the pole profile of a supercuspidal
orbit forces supercuspidality below and computes the size of the norm-twist stabilizer. -/
def CuspidalSelfPairDescentProfileStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : Type v) [Field E] [Algebra F.Carrier E] (n : ℕ), 0 < n →
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V),
      π.IsIrreducible → F.canonicalTopologicalData.IsSquareIntegrable π →
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
        (chars : Finset (F.Carrierˣ →* ℂˣ)),
        (∀ κ, κ ∈ chars ↔ IsNormTrivial E κ) →
        (∀ κ : chars, IsOpen (κ.val.ker : Set F.Carrierˣ)) →
        ∀ (f s : ℕ), 0 < f → ∀ (Q : ℂ[X]) (R : chars → ℂ[X]),
          (∀ κ : chars, IsPadicRankLPolynomial F ψ ν.val π
            (twist (κ.val.comp determinant) (smoothContragredient π)) (R κ)) →
          Q.eval ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ f) ≠ 0 →
          lPolynomialPoleOrderAtZero Q = s →
          Q.comp (X ^ f) = ∏ κ : chars, R κ →
          IsSupercuspidal π ∧ Nat.card (normTwistStabilizer E π) = s

set_option maxHeartbeats 1300000 in
/-- Evaluate at the residue cardinality to detect a segment of length one.
Compare multiplicities at one to count exactly the stabilizing twists. -/
theorem cuspidalSelfPairDescentProfile : CuspidalSelfPairDescentProfileStatement.{u,v,uV} := by
  classical
  intro p _ F E _ _ n hn
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ π hi hsq ψ ν chars hchars hopen f s hf Q R hR hQ horder hprod
  let oneChar : chars := ⟨1, (hchars 1).mpr (isNormTrivial_one E)⟩
  have h1 : IsPadicRankLPolynomial F ψ ν.val π (smoothContragredient π) (R oneChar) := by
    simpa only [oneChar, MonoidHom.one_comp, twist_one] using hR oneChar
  have hne : (R oneChar).eval (T.residueCardinality : ℂ) ≠ 0 := by
    intro hz
    have he := congrArg (Polynomial.eval (T.residueCardinality : ℂ)) hprod
    rw [eval_comp, eval_pow, eval_X, eval_prod, Finset.prod_eq_zero (Finset.mem_univ oneChar) hz] at he
    exact hQ he
  let A := SmoothRep.of π hsq.isAdmissible.1
  let e := A.universeLiftEquiv.{u}
  let ht := (IsPadicRankLPolynomial.congr_equiv e (smoothContragredientEquiv e).symm).mp h1
  have hsc := (isSupercuspidal_iff_of_equiv e).mpr
    (isSupercuspidal_of_squareIntegrable_selfPair_eval_ne_zero.{u,uV} F ψ ν hn A.universeLift
      ((isIrreducible_iff_of_equiv e).mp hi) ((T.isSquareIntegrable_iff_of_equiv e).mp hsq) ht hne)
  refine ⟨hsc, ?_⟩
  calc
    Nat.card (normTwistStabilizer E π) = ∑ κ : chars, lPolynomialPoleOrderAtZero (R κ) := by
      simp only [fun κ => lPolynomialPoleOrderAtZero_twistedSelfPair_supercuspidal F ψ ν hn π hi
        hsc κ.val (hopen κ) (hR κ)]
      exact (sum_normTwistStabilizer π chars hchars).symm
    _ = lPolynomialPoleOrderAtZero (∏ κ : chars, R κ) :=
      (lPolynomialPoleOrderAtZero_prod _ _ (fun κ _ => (hR κ).ne_zero)).symm
    _ = lPolynomialPoleOrderAtZero Q := by
      rw [← hprod, lPolynomialPoleOrderAtZero_comp_X_pow Q hf]
    _ = s := horder

end Langlands.BaseChange
