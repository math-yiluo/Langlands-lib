import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof
import Langlands.Representation.Derivative.MirabolicProductMinusCompatibility
import Langlands.Representation.Derivative.LeftMixedProductFirstDerivative
import Langlands.Representation.Derivative.RightMixedProductDerivativePositive
import Langlands.Representation.Derivative.RightMixedProductZeroRank
import Langlands.Representation.Derivative.LeibnizPositiveGluing
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof

/-! Positive-rank product derivative filtrations from actual minus identities. -/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Derivative.LocalPositiveLeibniz

open GeneralLinear HarmonicAnalysis

universe uF uV uW uC vC uD vD

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Peel the initial minus functor from a successor-order derivative, with
arbitrary source and final rank equalities retained. -/
theorem derivative_succ_cast {a b c : ℕ} (h : a = b + 1) (i : ℕ)
    (hi : 0 < i ∧ i ≤ b + 1) (hi' : 0 < i + 1 ∧ i + 1 ≤ a + 1)
    (ha : a + 1 - (i + 1) = c) (hb : b + 1 - i = c) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF,uW} T ψ a (i + 1) hi' ⋙
        generalLinearRankCast T ha =
      mirabolicRankCast T h ⋙ Mirabolic.phiMinus T ψ b ⋙
        mirabolicDerivativeOfOrder T ψ b i hi ⋙ generalLinearRankCast T hb := by
  let := T.topology
  subst h
  rw [RightMixedDerivative.derivative_succ_eq T ψ b i hi hi'
    (by omega : b + 1 - i = b + 1 + 1 - (i + 1))
    (generalLinearRankCast T ha)]
  simp only [mirabolicRankCast_refl, Functor.id_comp,
    generalLinearRankCast_trans]

/-- The successor derivative of a positive-rank left mixed product is the
previous derivative of the mixed product with `Φ⁻` in its second input. -/
def leftSourceSuccIso (k r i c : ℕ)
    (hi : 0 < i ∧ i ≤ (k + 1) + r + 1)
    (hc : (k + 1) + r + 1 - i = c) :
    letI := T.topology
    T.leftMixedProductFunctor.{uF,uV} (k + 1) (r + 1) ⋙
        mirabolicDerivativeOfOrder T ψ ((k + 1) + (r + 1)) (i + 1)
          ⟨by omega, by omega⟩ ⋙
        generalLinearRankCast T
          (show (k + 1) + (r + 1) + 1 - (i + 1) = c by omega) ≅
      (𝟭 _).prod (Mirabolic.phiMinus T ψ r) ⋙
        (T.leftMixedProductFunctor (k + 1) r ⋙
          mirabolicDerivativeOfOrder T ψ ((k + 1) + r) i hi ⋙
          generalLinearRankCast T hc) := by
  let := T.topology
  have hb : (k + (r + 1)) + 1 - i = c := by omega
  refine Functor.isoWhiskerLeft (T.leftMixedProductFunctor (k + 1) (r + 1))
      (eqToIso (derivative_succ_cast T ψ (Nat.succ_add k (r + 1)) i
        ⟨hi.1, by omega⟩ ⟨by omega, by omega⟩ _ hb)) ≪≫ ?_
  refine Functor.isoWhiskerRight
      (Classical.choice (MirabolicProductMinus.leftPhiCompatibility.{uF,uV} T ψ k r))
      (mirabolicDerivativeOfOrder T ψ (k + (r + 1)) i ⟨hi.1, by omega⟩ ⋙
        generalLinearRankCast T hb) ≪≫ ?_
  apply eqToIso
  simpa only [MirabolicProductMinus.leftPhiExpected, Functor.assoc, Functor.comp_id,
    Nat.add_succ] using
    RightMixedDerivative.derivative_transport T ψ (Nat.succ_add k r) i
      ⟨hi.1, by omega⟩ ⟨hi.1, by omega⟩ (by omega) hb
      ((𝟭 _).prod (Mirabolic.phiMinus T ψ r) ⋙ T.leftMixedProductFunctor (k + 1) r)
      (𝟭 _)

/-- Compensating a second-factor rank transport after binary induction cancels it. -/
theorem product_rankCast_cancel {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {k a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (X : C ⥤ SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier))
      (Y : D ⥤ SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)),
      X.prod (Y ⋙ generalLinearRankCast T h) ⋙ T.binaryNormalizedProductFunctor k b ⋙
          generalLinearRankCast T (congrArg (fun n => k + n) h.symm) =
        X.prod Y ⋙ T.binaryNormalizedProductFunctor k a := by
  let := T.topology
  subst h
  intros
  simp only [generalLinearRankCast_refl, Functor.comp_id]

/-- Iteration of the actual left minus identities at positive GL rank. -/
theorem leftIsoPos (k : ℕ) :
    letI := T.topology
    ∀ (r i : ℕ) (hi : 0 < i ∧ i ≤ r + 1),
      Nonempty
        (T.leftMixedProductFunctor.{uF,uV} (k + 1) r ⋙
            mirabolicDerivativeOfOrder T ψ ((k + 1) + r) i ⟨hi.1, by omega⟩ ⋙
            generalLinearRankCast T
              (show (k + 1) + r + 1 - i = (k + 1) + (r + 1 - i) by omega) ≅
          (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
            T.binaryNormalizedProductFunctor (k + 1) (r + 1 - i)) := by
  let := T.topology
  intro r
  induction r with
  | zero =>
      intro i hi
      obtain rfl : i = 1 := by omega
      exact ⟨leftMixedProductFirstDerivativeIso.{uF,uV} T ψ (k + 1) 0⟩
  | succ r ih =>
      intro i hi
      rcases i with _ | _ | j
      · omega
      · exact ⟨leftMixedProductFirstDerivativeIso.{uF,uV} T ψ (k + 1) (r + 1)⟩
      have hj : 0 < j + 1 ∧ j + 1 ≤ r + 1 := by omega
      have e₀ := leftSourceSuccIso.{uF,uV} T ψ k r (j + 1)
        ((k + 1) + (r + 1 - (j + 1))) ⟨hj.1, by omega⟩ (by omega)
      obtain ⟨e₁⟩ := ih (j + 1) hj
      have e₂ := e₀ ≪≫
        Functor.isoWhiskerLeft ((𝟭 _).prod (Mirabolic.phiMinus T ψ r)) e₁
      have hr : r + 1 + 1 - (j + 1 + 1) = r + 1 - (j + 1) := by omega
      have e₃ := Functor.isoWhiskerRight e₂
        (generalLinearRankCast T (congrArg (fun n => (k + 1) + n) hr.symm))
      refine ⟨eqToIso ?_ ≪≫ e₃ ≪≫ eqToIso ?_⟩
      · simp only [Functor.assoc, generalLinearRankCast_trans]
      · have hD := RightMixedDerivative.phiMinus_derivative_eq T ψ r (j + 1) hj hi hr
        change (𝟭 _).prod (Mirabolic.phiMinus T ψ r ⋙
            mirabolicDerivativeOfOrder T ψ r (j + 1) hj) ⋙
            T.binaryNormalizedProductFunctor (k + 1) (r + 1 - (j + 1)) ⋙
            generalLinearRankCast T (congrArg (fun n => (k + 1) + n) hr.symm) = _
        rw [hD]
        exact product_rankCast_cancel T hr (𝟭 _)
          (mirabolicDerivativeOfOrder T ψ (r + 1) (j + 1 + 1) hi)

/-- Equality-based rank transport preserves a zero carrier. -/
theorem rankCast_subsingleton {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uW} ℂ (GeneralLinear a F.Carrier),
      Subsingleton A → Subsingleton ((generalLinearRankCast T h).obj A) := by
  subst h
  exact fun _ hA => hA

/-- Above the second factor's rank, derivatives of positive-rank left mixed
products vanish by iteration of the actual `P₁` minus boundary. -/
theorem leftVanishPos (k : ℕ) :
    letI := T.topology
    ∀ (r i : ℕ) (hi : 0 < i ∧ i ≤ (k + 1) + r + 1),
      r + 1 < i →
      ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + 1) F.Carrier))
        (B : SmoothRep.{0,uF,uV} ℂ (mirabolic r F.Carrier)),
        Subsingleton ((mirabolicDerivativeOfOrder T ψ ((k + 1) + r) i hi).obj
          ((T.leftMixedProductFunctor (k + 1) r).obj (A, B))) := by
  let := T.topology
  intro r
  induction r with
  | zero =>
      intro i hi hlarge A B
      rcases i with _ | _ | j
      · omega
      · omega
      have hj : 0 < j + 1 ∧ j + 1 ≤ k + 1 := by omega
      have hz := MirabolicProductMinus.leftPhiBoundary.{uF,uV} T ψ k (A, B)
      have hZ := mirabolicDerivativeOfOrder_obj_subsingleton T ψ k (j + 1) hj
        ((MirabolicProductMinus.leftPhiProduct T ψ k 0).obj (A, B)) hz
      have hc : k + 1 - (j + 1) = (k + 1) + 0 + 1 - (j + 1 + 1) := by omega
      have hZ' := rankCast_subsingleton T hc _ hZ
      change Subsingleton
        ((mirabolicDerivativeOfOrder T ψ ((k + 1) + 0) (j + 1 + 1) hi ⋙
          generalLinearRankCast T (rfl : _ = _)).obj
          ((T.leftMixedProductFunctor (k + 1) 0).obj (A, B)))
      rw [derivative_succ_cast T ψ (by omega : (k + 1) + 0 = k + 1)
        (j + 1) hj hi rfl hc]
      exact hZ'
  | succ r ih =>
      intro i hi hlarge A B
      rcases i with _ | _ | j
      · omega
      · omega
      have hj : 0 < j + 1 ∧ j + 1 ≤ (k + 1) + r + 1 := by omega
      have hZ := ih (j + 1) hj (by omega) A ((Mirabolic.phiMinus T ψ r).obj B)
      let e := (leftSourceSuccIso.{uF,uV} T ψ k r (j + 1)
        ((k + 1) + r + 1 - (j + 1)) hj rfl).app (A, B)
      have hz := (LevelCalculus.subsingleton_iff_of_iso e).2 hZ
      have hc : (k + 1) + r + 1 - (j + 1) =
          (k + 1) + (r + 1) + 1 - (j + 1 + 1) := by omega
      have hz' := rankCast_subsingleton T hc _ hz
      change Subsingleton ((generalLinearRankCast T hc.symm ⋙
          generalLinearRankCast T hc).obj
          ((mirabolicDerivativeOfOrder T ψ ((k + 1) + (r + 1))
            (j + 1 + 1) hi).obj
            ((T.leftMixedProductFunctor (k + 1) (r + 1)).obj (A, B)))) at hz'
      rw [generalLinearRankCast_symm_comp] at hz'
      exact hz'

/-- Positive-rank and positive-order Leibniz gluing with every actual
mixed-product premise discharged. -/
theorem positiveGlued (m n i : ℕ) (hi : 0 < i ∧ i ≤ (m + 1) + (n + 1)) :
    IsGluedFromFamily (leibnizSource.{uF,uV} T ψ (m + 1) (n + 1) i hi.2)
      (leibnizPiece T ψ (m + 1) (n + 1) i) :=
  leibnizSource_glued_pos.{uF,uV} T (leftMixedProductDerivativeIso.{uF,uV} F T)
    (leftMixedProductDerivativeVanishing.{uF,uV} F T)
    (rightMixedProductDerivativeFiltration.{uF,uV} F T) ψ m n i hi

end Langlands.Derivative.LocalPositiveLeibniz

namespace Langlands.Derivative

universe uF uV

/-- The actual positive-order derivative of a product with both ranks positive
is glued from all feasible actual product derivatives. -/
def PositiveRankDerivativeLeibnizGluing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n i : ℕ) (hi : 0 < i ∧ i ≤ (m + 1) + (n + 1)),
    IsGluedFromFamily (leibnizSource.{uF,uV} T ψ (m + 1) (n + 1) i hi.2)
      (leibnizPiece T ψ (m + 1) (n + 1) i)

/-- The published actual minus compatibilities imply positive-rank
Leibniz gluing. -/
theorem positiveRankDerivativeLeibnizGluing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    PositiveRankDerivativeLeibnizGluing.{uF,uV} F T :=
  LocalPositiveLeibniz.positiveGlued.{uF,uV} T

end Langlands.Derivative
