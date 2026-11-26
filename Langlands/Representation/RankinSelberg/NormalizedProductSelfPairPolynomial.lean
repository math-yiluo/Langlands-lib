import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.Representation.RankinSelberg.BlockShapeSmoothDualGamma
import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.RankinSelberg.TemperedLFactorProof

/-! # The self-pair denominator of a normalized product of discrete series -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis _root_.Polynomial

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance productTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
private local instance productGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {n : ℕ} (B : BlockShape n) {V : Fin B.length → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (R : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))

set_option maxHeartbeats 1000000 in
private theorem exists_normalizedProductSelfPairPolynomials (hn : 0 < n)
    (hI : ∀ i, (R i).IsIrreducible)
    (hS : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (R i)) :
    ∃ D : Fin B.length → Fin B.length → ℂ[X],
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val (R i) (smoothContragredient (R j)) (D i j)) ∧
      IsPadicRankLPolynomial F ψ ν.val (F.canonicalNormalizedProductInduced B R)
        (smoothContragredient (F.canonicalNormalizedProductInduced B R)) (∏ i, ∏ j, D i j) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    let T := F.canonicalTopologicalData
    let Rdual := fun i => smoothContragredient (R i)
    have hA (i : Fin B.length) := (hS i).isAdmissible
    have hId (i : Fin B.length) : (Rdual i).IsIrreducible := by
      let X := SmoothRep.of (R i) (hA i).1
      exact (X.isIrreducible_contragredient_iff (compactOpen_cofinal F T (B.size i)) (hA i)).mpr (hI i)
    have hSd (i : Fin B.length) : T.IsSquareIntegrable (Rdual i) :=
      T.isSquareIntegrable_smoothContragredient (R i) (hS i)
    obtain ⟨Q, D, hQ, hD, hprod⟩ := TemperedLFactorStatement.blockShape F ψ ν
      temperedLFactor B B R Rdual hI hS hId hSd
    let e := T.normalizedProductSmoothDualEquiv B R hA
    refine ⟨D, hD, ?_⟩
    rw [← hprod]
    exact (IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl _) e).mpr hQ

/-- The certified block-pair denominators and their product certificate for
the actual smooth contragredient of the induced discrete-series product. -/
def normalizedProductSelfPairPolynomials (hn : 0 < n)
    (hI : ∀ i, (R i).IsIrreducible)
    (hS : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (R i)) :
    {D : Fin B.length → Fin B.length → ℂ[X] //
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val (R i) (smoothContragredient (R j)) (D i j)) ∧
      IsPadicRankLPolynomial F ψ ν.val (F.canonicalNormalizedProductInduced B R)
        (smoothContragredient (F.canonicalNormalizedProductInduced B R)) (∏ i, ∏ j, D i j)} :=
  Classical.indefiniteDescription _ (exists_normalizedProductSelfPairPolynomials F ψ ν B R hn hI hS)

end Langlands.RankinSelberg
