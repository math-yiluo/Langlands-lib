import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement

/-!
# The ordinary two-block Jacquet integral as a nonzero Whittaker functional

JPSS 1983, Section (4.6), printed pages 410-411. For blocks `τ_1, τ_2` of Whittaker
type and the opposite real twists `σ_1 = τ_1 ⊗ α^(-u)`, `σ_2 = τ_2 ⊗ α^u`, the source
shows that for `u ≫ 0` the integral (4.6.2) converges for every section of the lower
induction `σ_u`, and that the resulting function of `g` belongs to `W(σ_u; ψ̄)`. This
module states the integral realization behind that claim: for `u` above one bound,
every section is absolutely integrable, and the ordinary integrals are the coefficients
`g ↦ J(σ_u(g) f)` of one nonzero inverse-character Whittaker functional `J` on the
actual induced representation. It proves nothing, and it does not compare `J` with
other Whittaker functionals of `σ_u`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

/-- JPSS 1983, Section (4.6), printed pages 410-411: for blocks `τ_1, τ_2` of full
standard Whittaker type and supplied nonzero inverse-character functionals `ℓ_1, ℓ_2`,
there is a real bound `C` such that for every real `u > C`, writing `σ_u` for the actual
lower induction of `(τ_1 |det|^(-u), τ_2 |det|^u)` and `μ` for the product of the
supplied self-dual Haar measure,

* the raw integrand of (4.6.2) of every section is absolutely integrable at every
  ambient element, and
* there is a nonzero `ψ⁻¹`-equivariant functional `J` on `σ_u` with
  `J(σ_u(g) f) = ∫ (ℓ_1 ⊗ ℓ_2)(f(u(x) g)) ψ(x_(m_0,0)) dμ(x)` for every section `f` and
  every `g`. -/
def TwoBlockOrdinaryJacquetFunctionalStatement.{uF, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
      ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i), (∀ i, (ell i).val ≠ 0) →
      ∃ C : ℝ, ∀ u : ℝ, C < u →
        (∀ f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u),
          TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val)
            (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f) ∧
        ∃ J : glInverseFunctionals ψ t
            (TwoBlockJacquet.inducedRep F h (twoBlockOppositeTwistBlocks F m τ u)),
          J.val ≠ 0 ∧
          ∀ (f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u))
            (g : Langlands.GeneralLinear (t + 1) F.Carrier),
            J.val (TwoBlockJacquet.inducedRep F h (twoBlockOppositeTwistBlocks F m τ u) g f) =
              TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
                (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g

end Langlands.RankinSelberg
