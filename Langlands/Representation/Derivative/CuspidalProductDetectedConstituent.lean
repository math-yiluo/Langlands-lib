import Langlands.Representation.Filtration.ExactFunctorDetectedConstituent
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Langlands.Representation.Derivative.FiniteTopLine
import Langlands.Representation.Derivative.TopLine
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Induction.BlockEquivalence

/-! Actual nondegenerate constituent data for a fixed ordered cuspidal product. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Derivative

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

private def positiveCuspidalTopLine {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (hirr : letI := T.topology; A.IsIrreducible)
    (hsc : letI := T.topology; IsSupercuspidal A.representation) :
    letI := T.topology
    ((generalLinearDerivative T ψ r r le_rfl).obj A) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  cases r with
  | zero => exact (Nat.not_lt_zero _ hr).elim
  | succ m =>
    exact topDerivativeLineEquiv T ψ m A hirr hsc.1
      (Classification.SupercuspidalTopDerivative.nontrivial_generalLinearDerivative_top
        T ψ m A hsc
        (Classification.SupercuspidalTopDerivative.nontrivial_of_isIrreducible
          A.representation hirr))

set_option maxHeartbeats 800000 in
/-- The whole top derivative of a positive-rank ordered product of actual
supercuspidal factors is linearly equivalent to the complex scalars. -/
def cuspidalProductTopDerivativeLineEquiv {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  let σ : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear (B.size i) F.Carrier) :=
    fun i => SmoothRep.universeLift.{uF} (C i).obj
  have hirr (i) : (σ i).IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff (C i).obj).mpr (C i).property.1
  have hsc (i) : IsSupercuspidal (σ i).representation :=
    isSupercuspidal_of_equiv
      (SmoothRep.universeLiftEquiv.{uF} (C i).obj) (C i).property.2
  let e : ∀ i, ((generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj
      (σ i)) ≃ₗ[ℂ] ℂ :=
    fun i => positiveCuspidalTopLine T ψ (B.positive i) (σ i) (hirr i) (hsc i)
  let P := (T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)
  let Q := (T.normalizedProductInductionFunctor B).obj σ
  let E : P ≅ Q := SmoothRep.mkIso
    (T.normalizedProductInducedEquiv B
      (fun i => SmoothRep.universeLiftEquiv.{uF} (C i).obj))
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  exact (SmoothRep.equivOfIso (J.mapIso E)).toLinearEquiv.trans
    (finiteProductTopDerivativeLineEquiv T ψ hn B σ e)

/-- Actual selected constituent and top-line data for one fixed ordered product.
The equivalences in `detected` concern the same ambient product. -/
structure CuspidalProductDetectedConstituentData {n : ℕ}
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) where
  topLine : letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))) ≃ₗ[ℂ] ℂ
  finite_length : letI := T.topology
    ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)).HasFiniteLength
  detected : letI := T.topology
    ExactFunctorDetectedConstituent.Data (generalLinearDerivative T ψ n n le_rfl)
      ((T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj))

/-- Choose the unique nondegenerate irreducible constituent class of a fixed
positive-rank ordered supercuspidal product, as actual constituent data. -/
def chooseCuspidalProductDetectedConstituent {n : ℕ} (hn : 0 < n)
    (B : BlockShape n)
    (C : letI := T.topology;
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    CuspidalProductDetectedConstituentData T ψ B C := by
  letI := T.topology
  let P := (T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  let e := cuspidalProductTopDerivativeLineEquiv T ψ hn B C
  have hP : P.HasFiniteLength :=
    Classification.irreducibleProductFiniteLength F T n hn B
      (fun i => (C i).obj) (fun i => (C i).property.1)
  have hJ : Mirabolic.MapsShortExactIntertwiners J :=
    generalLinearDerivativeExactness F T ψ n n le_rfl
  letI := ExactFunctorIrreducibility.preservesZero_of_exact J hJ
  have hirr : (J.obj P).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one (J.obj P)
      (e.finrank_eq.trans (Module.finrank_self ℂ))
  exact
    { topLine := e
      finite_length := hP
      detected := ExactFunctorDetectedConstituent.choose J hJ P hP hirr }

end Langlands.Derivative
