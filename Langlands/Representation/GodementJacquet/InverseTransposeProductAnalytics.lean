import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Induction.OppositeProductReversalProof

/-!
# Inverse-transpose analytics and the reversed ordered block family

The published upper-to-opposite and opposite-to-reversed-upper transports are
composed as actual representation equivalences. Coefficient transport then
identifies the transformed analytic predicate with the ordinary predicate on
this reversed family, retaining the prescribed measure and polynomial.
-/

noncomputable section

namespace Langlands.GodementJacquet

universe uF uV

open MeasureTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {V : Fin B.length → Type uV} [hadd : ∀ i, AddCommGroup (V i)]
  [hmod : ∀ i, Module ℂ (V i)]

/-- The inverse-transpose pullback of the actual upper product induction is
equivalent to the reversed upper product of the inverse-transpose factors.
The reversal includes the entire dependent carrier family. -/
def inverseTransposeProductReversalEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
    Representation.Equiv
      ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
        (fun i => (σ i.rev).comp
          (GeneralLinear.inverseTranspose (B.size i.rev) F.Carrier).toMonoidHom)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let σθ := fun i => (σ i).comp
    (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom
  have hσθ : ∀ i, IsSmooth (σθ i) := fun i =>
    isSmooth_comp (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom
      (GeneralLinear.continuous_inverseTranspose _ _) (hσ i)
  exact (T.inverseTransposeProductToOppositeEquiv B σ).trans
    (Classical.choose (glOppositeProductReversal p F T n B V σθ hσθ))

/-- The transformed analytic assertions for the original actual product
induction are exactly the ordinary assertions for the reversed upper product
of the pulled-back factors. The polynomial and measure are unchanged. -/
theorem iotaMatrixAnalyticAssertions_product_iff
    {r : ℕ} [MeasurableSpace (GeneralLinear (r + 1) F.Carrier)]
    (B : GeneralLinear.BlockShape (r + 1))
    {V : Fin B.length → Type uV} [hadd : ∀ i, AddCommGroup (V i)]
    [hmod : ∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i))
    (q : ℕ) (abv : AbsoluteValue F.Carrier ℝ)
    (μ : Measure (GeneralLinear (r + 1) F.Carrier)) (P : Polynomial ℂ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (r + 1)
    letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
    IotaMatrixAnalyticAssertions q abv μ (T.normalizedProductInduced B σ) P ↔
      MatrixAnalyticAssertions q abv μ
        (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
          (fun i => (σ i.rev).comp
            (GeneralLinear.inverseTranspose (B.size i.rev) F.Carrier).toMonoidHom)) P := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  exact (iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose q abv μ P).trans
    (matrixAnalyticAssertions_equiv q abv μ
      (inverseTransposeProductReversalEquiv T B σ hσ) P)

end Langlands.GodementJacquet
