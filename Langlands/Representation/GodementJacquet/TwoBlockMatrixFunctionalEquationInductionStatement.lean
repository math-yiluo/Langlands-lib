import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.Classification.ConstituentCompatibility

/-!
# Conditional two-block normalized matrix functional equation

The functional-equation part of Godement–Jacquet 1972, Theorem 3.4 (printed
pages 36–45), with two blocks, for split `GL` over a canonical p-adic field, in
the transpose Fourier convention of JPS 1979, printed page 177. The statement is
conditional: the block normalized matrix data are premises, and the blocks may
be reducible. This module only states the proposition.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

/-- Godement–Jacquet 1972, Theorem 3.4 (printed page 36), functional-equation
part, with two blocks. Let `σ i` be smooth admissible, not necessarily
irreducible, representations of `GL_(m i + 1)(F)` with scalar central
quasicharacters `ω i`, let `ψ` be a nontrivial additive character and `ν` a
Haar measure self-dual for `ψ`. If each block has normalized matrix
functional-equation data `(P i, PDual i, c i, a i)` for `ψ` and `ν`, then the
actual normalized induction of `(σ 0, σ 1)` to `GL_(t+1)(F)` has normalized
matrix functional-equation data with the products of the polynomials, the
product of the units and the sum of the exponents, for the same `ψ` and `ν`. -/
def TwoBlockMatrixFunctionalEquationInductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i)),
      (∀ i, Langlands.IsSmooth (σ i)) →
      (∀ i, Langlands.IsAdmissible (σ i)) →
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ ν →
      ∀ (ω : Fin 2 → Quasicharacter F.Carrier),
      (∀ i, Classification.HasGLCentralCharacter F.Carrier (m i + 1) (σ i)
        (ω i : F.Carrierˣ →* ℂˣ)) →
      ∀ (P PDual : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ),
      (∀ i, Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
        (P i) (PDual i) (c i) (a i)) →
      Padic.NormalizedMatrixFunctionalEquationData F ψ ν
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
        (∏ i, P i) (∏ i, PDual i) (∏ i, c i) (∑ i, a i)

end Langlands.GodementJacquet
