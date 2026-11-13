import Langlands.Representation.Classification.BernsteinUnitaryProductReduction
import Langlands.Representation.Classification.BernsteinBinaryRankZero
import Langlands.Representation.Classification.BernsteinLowerDerivativePositivityStatement
import Langlands.Representation.Classification.BernsteinProductPositivityStatement
import Langlands.Representation.Classification.BernsteinUnitaryIrreducibilityCriterionStatement
import Langlands.Representation.Derivative.ShiftedHighestProduct
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Unitary.Restriction
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! Bernstein's binary rank induction from the four separate analytic inputs. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis CentralEigenspaceSplitting

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The four separate analytic inputs used by Bernstein's rank induction.
This package makes no assertion that any of its four clauses is proved. -/
def BernsteinUnitaryInductionInputs : Prop :=
  BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T ∧
    BernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T ∧
      BernsteinUnitaryTopDerivativeProductPositivity.{uF, uV} F T ∧
        BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T

private theorem nontrivial_of_irreducible {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : Representation.IsIrreducible ρ) : Nontrivial V := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible hρ
  exact ⟨⟨v, 0, hv⟩⟩

private theorem pair_of_iso {G : Type uF} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uF, max uF uV} ℂ G}
    (e : A ≅ B)
    (hB : Representation.IsIrreducible B.representation ∧ IsUnitarizable B.representation) :
    Representation.IsIrreducible A.representation ∧ IsUnitarizable A.representation :=
  ⟨(isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hB.1,
    (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hB.2⟩

private theorem pair_rankCast {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology
      Representation.IsIrreducible A.representation ∧ IsUnitarizable A.representation) :
    letI := T.topology
    Representation.IsIrreducible ((Derivative.generalLinearRankCast T h).obj A).representation ∧
      IsUnitarizable ((Derivative.generalLinearRankCast T h).obj A).representation := by
  subst b
  exact hA

private theorem binary_unitarizable (a b : ℕ)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hAi : letI := T.topology; Representation.IsIrreducible A.representation)
    (hAu : letI := T.topology; IsUnitarizable A.representation)
    (hBi : letI := T.topology; Representation.IsIrreducible B.representation)
    (hBu : letI := T.topology; IsUnitarizable B.representation) :
    letI := T.topology
    IsUnitarizable ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
  let := T.topology
  by_cases ha : a = 0
  · subst a
    let e := (T.binaryNormalizedProductFunctor 0 b).mapIso
      ((rankZeroIrreducibleUnitIso F T A hAi).prod (Iso.refl B))
    apply (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mpr
    apply (isUnitarizable_iff_of_equiv (T.binaryProductLeftUnitEquiv B)).mpr
    exact (isUnitarizable_iff_of_equiv (BinaryTensor.liftEquiv _)).mp (hBu.comp _)
  by_cases hb : b = 0
  · subst b
    let e := (T.binaryNormalizedProductFunctor a 0).mapIso
      ((Iso.refl A).prod (rankZeroIrreducibleUnitIso F T B hBi))
    apply (isUnitarizable_iff_of_equiv (SmoothRep.equivOfIso e)).mpr
    apply (isUnitarizable_iff_of_equiv (T.binaryProductRightUnitEquiv A)).mpr
    exact (isUnitarizable_iff_of_equiv (BinaryTensor.liftEquiv _)).mp (hAu.comp _)
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  let σ := (T.binaryPairFamilyFunctor hapos hbpos).obj (A, B)
  have hσ : ∀ i, IsUnitarizable (σ i).representation := by
    intro i
    fin_cases i
    · exact hAu
    · exact hBu
  apply (isUnitarizable_iff_of_equiv
    (SmoothRep.equivOfIso ((T.binaryNormalizedProductPositiveIso hapos hbpos).app (A, B)))).mpr
  exact glNormalizedProductInductionUnitarity.{uF, uV} p F T (a + b) (by omega)
    (BlockShape.binary a b hapos hbpos) σ hσ

private theorem binary_positive_step
    (hhighest : BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T)
    (hlower : BernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T)
    (hproduct : BernsteinUnitaryTopDerivativeProductPositivity.{uF, uV} F T)
    (hcriterion : BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hAi : letI := T.topology; Representation.IsIrreducible A.representation)
    (hAu : letI := T.topology; IsUnitarizable A.representation)
    (hBi : letI := T.topology; Representation.IsIrreducible B.representation)
    (hBu : letI := T.topology; IsUnitarizable B.representation)
    (ih : letI := T.topology
      ∀ (a' b' : ℕ), a' + b' < a + b →
        ∀ (A' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a' F.Carrier))
          (B' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b' F.Carrier)),
          Representation.IsIrreducible A'.representation → IsUnitarizable A'.representation →
          Representation.IsIrreducible B'.representation → IsUnitarizable B'.representation →
            Representation.IsIrreducible
                ((T.binaryNormalizedProductFunctor a' b').obj (A', B')).representation ∧
              IsUnitarizable
                ((T.binaryNormalizedProductFunctor a' b').obj (A', B')).representation) :
    letI := T.topology
    Representation.IsIrreducible
        ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation ∧
      IsUnitarizable ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
  let := T.topology
  let P := (T.binaryNormalizedProductFunctor a b).obj (A, B)
  have hPu : IsUnitarizable P.representation :=
    binary_unitarizable F T a b A B hAi hAu hBi hBu
  have hAl := SmoothRep.hasFiniteLength_of_isIrreducible hAi
  have hBl := SmoothRep.hasFiniteLength_of_isIrreducible hBi
  let hdA := Derivative.chooseGeneralLinearHighestDerivativeOrder T ψ ha A
    (nontrivial_of_irreducible hAi)
  let hdB := Derivative.chooseGeneralLinearHighestDerivativeOrder T ψ hb B
    (nontrivial_of_irreducible hBi)
  have hAtop := hhighest a ha ψ A hAi hAu hdA
  have hBtop := hhighest b hb ψ B hBi hBu hdB
  let X := shiftedHighestDerivative F T ψ hdA
  let Y := shiftedHighestDerivative F T ψ hdB
  have hleA := hdA.le_rank
  have hleB := hdB.le_rank
  have hposA := hdA.positive
  have hposB := hdB.positive
  have hsum : hdA.order + hdB.order ≤ a + b := by omega
  have hsmall : (a - hdA.order) + (b - hdB.order) < a + b := by omega
  have hXY := ih (a - hdA.order) (b - hdB.order) hsmall X Y
    hAtop.1 hAtop.2 hBtop.1 hBtop.2
  let h : (a - hdA.order) + (b - hdB.order) = (a + b) - (hdA.order + hdB.order) := by omega
  have hcast := pair_rankCast F T h
    ((T.binaryNormalizedProductFunctor (a - hdA.order) (b - hdB.order)).obj (X, Y)) hXY
  have htop := pair_of_iso
    (A := bernsteinShiftedDerivative T ψ P (hdA.order + hdB.order) hsum)
    (B := (Derivative.generalLinearRankCast T h).obj
      ((T.binaryNormalizedProductFunctor (a - hdA.order) (b - hdB.order)).obj (X, Y)))
    (Derivative.HighestProduct.shiftedHighestProductIso T ψ A B
      hdA.order hdB.order hdA.le_rank hdB.le_rank hdA.higher_vanish hdB.higher_vanish hsum)
    hcast
  have hPnonzero : Nontrivial
      ((Derivative.generalLinearDerivative T ψ (a + b) (hdA.order + hdB.order) hsum).obj P) :=
    nontrivial_of_irreducible htop.1
  let hdP : Derivative.GeneralLinearHighestDerivativeOrderData T ψ P :=
    { order := hdA.order + hdB.order
      le_rank := hsum
      positive := by omega
      nonzero := hPnonzero
      higher_vanish := Derivative.HighestProduct.subsingleton_above T ψ A B
        hdA.order hdB.order hdA.higher_vanish hdB.higher_vanish }
  have hPpositive := hproduct ψ a b A B hAl hBl
    hdA.order hdB.order hdA.le_rank hdB.le_rank hdA.higher_vanish hdB.higher_vanish
    (hlower a ha ψ A hAi hAu hdA) (hlower b hb ψ B hBi hBu hdB) hAtop.2 hBtop.2
  have hPl := Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength
    T (A, B) hAl hBl
  exact ⟨hcriterion (a + b) (by omega) ψ P hPl hPu hdP hPpositive htop.1 htop.2, hPu⟩

private theorem allRank_binary_of_inputs
    (hinputs : BernsteinUnitaryInductionInputs.{uF, uV} F T) :
    letI := T.topology
    ∀ (a b : ℕ)
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      Representation.IsIrreducible A.representation → IsUnitarizable A.representation →
      Representation.IsIrreducible B.representation → IsUnitarizable B.representation →
        Representation.IsIrreducible
            ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation ∧
          IsUnitarizable ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
  let := T.topology
  rcases hinputs with ⟨hhighest, hlower, hproduct, hcriterion⟩
  obtain ⟨ψ⟩ := padicUnitaryAdditiveCharacterExists F T
  have hall : ∀ N a b, a + b = N →
      ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
        (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
        Representation.IsIrreducible A.representation → IsUnitarizable A.representation →
        Representation.IsIrreducible B.representation → IsUnitarizable B.representation →
          Representation.IsIrreducible
              ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation ∧
            IsUnitarizable ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro a b hab A B hAi hAu hBi hBu
      by_cases ha : a = 0
      · subst a
        exact ⟨bernstein_binary_leftZero_irreducible F T b A B hAi hBi,
          binary_unitarizable F T 0 b A B hAi hAu hBi hBu⟩
      by_cases hb : b = 0
      · subst b
        exact ⟨bernstein_binary_rightZero_irreducible F T a A B hAi hBi,
          binary_unitarizable F T a 0 A B hAi hAu hBi hBu⟩
      apply binary_positive_step F T hhighest hlower hproduct hcriterion ψ a b
        (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) A B hAi hAu hBi hBu
      intro a' b' hlt A' B' hAi' hAu' hBi' hBu'
      exact ih (a' + b') (by omega) a' b' rfl A' B' hAi' hAu' hBi' hBu'
  intro a b A B hAi hAu hBi hBu
  exact hall (a + b) a b rfl A B hAi hAu hBi hBu

/-- The four independent analytic inputs give the exact published finite-block
unitary-product proposition, by binary rank induction and block regrouping. -/
theorem bernsteinUnitaryProductIrreducibility_of_inductionInputs
    (hinputs : BernsteinUnitaryInductionInputs.{uF, uV} F T) :
    BernsteinUnitaryProductIrreducibility.{uF, uV} F T := by
  apply bernsteinUnitaryProductIrreducibility_of_binary F T
  intro a b _ha _hb A B hAi hAu hBi hBu
  exact (allRank_binary_of_inputs F T hinputs a b A B hAi hAu hBi hBu).1

end Langlands.Classification
