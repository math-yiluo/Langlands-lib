import Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement
import Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement
import Langlands.Representation.GodementJacquet.FunctionalEquationProducts
import Langlands.Representation.GodementJacquet.ZetaLinear
import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.LocalField.Normalization.Proof

/-!
# Assembly of the two-block normalized functional equation

The closed two-block functional-equation statement follows from the two-block
analytic statement and a matched expansion of the induced zeta integral and its
transformed integral into finite sums of products of block zeta integrals with the
same block data. See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

/-- Matched expansion of induced zeta integrals (internal interface). Under the
hypotheses of the two-block functional-equation statement, for every full-matrix
test `Φ` and every coefficient `f = ⟨ℓ, I(g) v⟩` of a smooth functional and a smooth
vector of the normalized induced representation `I` there are finitely many block
tests `Ψ0 j`, `Ψ1 j` and block coefficients `f0 j`, `f1 j` such that, on a right
half-plane, `Z(Φ, s + t/2, f) = ∑ j, Z(Ψ0 j, s + m0/2, f0 j) Z(Ψ1 j, s + m1/2, f1 j)`,
and, on a right half-plane, the same identity holds for the full Fourier transforms
of the tests and the inverse-transpose transforms of the same coefficients. -/
def TwoBlockMatchedZetaExpansionStatement : Prop :=
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
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
        (hsd : IsSelfDual ψ ν),
      ∀ (ω : Fin 2 → Quasicharacter F.Carrier),
      (∀ i, Classification.HasGLCentralCharacter F.Carrier (m i + 1) (σ i)
        (ω i : F.Carrierˣ →* ℂˣ)) →
      ∀ (P PDual : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ),
      (∀ i, Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
        (P i) (PDual i) (c i) (a i)) →
      ∀ (Φ : MatrixTestFunction t F.Carrier)
        (ℓ : SmoothDual (F.canonicalNormalizedProductInduced (succBlockShape m h) σ))
        (v : smoothVectors (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)),
      ∃ (M : ℕ) (Ψ0 : Fin M → MatrixTestFunction (m 0) F.Carrier)
        (Ψ1 : Fin M → MatrixTestFunction (m 1) F.Carrier)
        (f0 : Fin M → biSmoothMatrixCoefficients (σ 0))
        (f1 : Fin M → biSmoothMatrixCoefficients (σ 1)),
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Padic.matrixIntegral F Φ (s + jpssShift t)
              (biSmoothCoefficient
                (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) ℓ v) =
            ∑ j, Padic.matrixIntegral F (Ψ0 j) (s + jpssShift (m 0)) (f0 j).val *
              Padic.matrixIntegral F (Ψ1 j) (s + jpssShift (m 1)) (f1 j).val) ∧
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ)
              (s + jpssShift t)
              (coefficientIota (biSmoothCoefficient
                (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) ℓ v)) =
            ∑ j, Padic.matrixIntegral F
                (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ0 j))
                (s + jpssShift (m 0)) (coefficientIota (f0 j).val) *
              Padic.matrixIntegral F
                (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ1 j))
                (s + jpssShift (m 1)) (coefficientIota (f1 j).val))

/-- The two-block functional-equation statement follows from the two-block analytic
statement and the matched expansion. -/
theorem twoBlockMatrixFunctionalEquationInduction_of_expansion
    (hexp : TwoBlockMatchedZetaExpansionStatement.{uF, uV})
    (han : TwoBlockMatrixAnalyticInductionStatement.{uF, uV}) :
    TwoBlockMatrixFunctionalEquationInductionStatement.{uF, uV} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  -- the Borel structures on the groups used by the canonical p-adic zeta integrals
  let (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
  have (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  intro t m h V hadd hmod σ hsm had ψ ν hsd ω hω P PD c a hdata
  have hAn := han p F t m h V σ ψ ν hsd ω hω hsm had P PD c a hdata
  refine ⟨hAn.1, hAn.2, fun Φ => ?_⟩
  refine ⟨rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ, fun x =>
    ⟨rectangularFourierEquiv_integrable ψ ν (t + 1) (t + 1) hsd Φ x,
      rectangularFourierEquiv_apply ψ ν (t + 1) (t + 1) hsd Φ x⟩, ?_⟩
  intro f R RD hR hRD
  -- the matched expansion extends from generators to the whole coefficient span,
  -- using the common convergence half-planes of the analytic statement
  obtain ⟨b1, hb1⟩ := hAn.1.1
  obtain ⟨b2, hb2⟩ := hAn.2.1
  have hspan : ∀ x ∈ biSmoothMatrixCoefficients
      (F.canonicalNormalizedProductInduced (succBlockShape m h) σ),
      ∃ (M : ℕ) (Ψ0 : Fin M → MatrixTestFunction (m 0) F.Carrier)
        (Ψ1 : Fin M → MatrixTestFunction (m 1) F.Carrier)
        (f0 : Fin M → biSmoothMatrixCoefficients (σ 0))
        (f1 : Fin M → biSmoothMatrixCoefficients (σ 1)),
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Padic.matrixIntegral F Φ (s + jpssShift t) x =
            ∑ j, Padic.matrixIntegral F (Ψ0 j) (s + jpssShift (m 0)) (f0 j).val *
              Padic.matrixIntegral F (Ψ1 j) (s + jpssShift (m 1)) (f1 j).val) ∧
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ)
              (s + jpssShift t) (coefficientIota x) =
            ∑ j, Padic.matrixIntegral F
                (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ0 j))
                (s + jpssShift (m 0)) (coefficientIota (f0 j).val) *
              Padic.matrixIntegral F
                (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ1 j))
                (s + jpssShift (m 1)) (coefficientIota (f1 j).val)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ℓ, v, rfl⟩ := hx
      exact hexp p F t m h V σ hsm had ψ ν hsd ω hω P PD c a hdata Φ ℓ v
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨0, fun s _ => ?_⟩,
        ⟨0, fun s _ => ?_⟩⟩
      · have h0 := matrixIntegral_smul (abv := normalizedAbsoluteValue F.canonicalTopologicalData)
          (μ := generalLinearHaar F.Carrier t) (Φ := Φ) (s := s + jpssShift t)
          (f := (0 : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ)) 0
        rw [zero_smul, zero_mul] at h0
        simpa [Padic.matrixIntegral] using h0
      · have h0 := matrixIntegral_smul (abv := normalizedAbsoluteValue F.canonicalTopologicalData)
          (μ := generalLinearHaar F.Carrier t)
          (Φ := rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ) (s := s + jpssShift t)
          (f := (0 : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ)) 0
        rw [zero_smul, zero_mul] at h0
        have hι : coefficientIota (0 : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ) = 0 := rfl
        simpa [Padic.matrixIntegral, hι] using h0
    | add x y hx hy ihx ihy =>
      obtain ⟨M, Ψ0, Ψ1, f0, f1, ⟨c1, hc1⟩, ⟨d1, hd1⟩⟩ := ihx
      obtain ⟨M', Ψ0', Ψ1', f0', f1', ⟨c2, hc2⟩, ⟨d2, hd2⟩⟩ := ihy
      refine ⟨M + M', Fin.append Ψ0 Ψ0', Fin.append Ψ1 Ψ1', Fin.append f0 f0',
        Fin.append f1 f1', ⟨max (max c1 c2) b1, fun s hs => ?_⟩,
        ⟨max (max d1 d2) b2, fun s hs => ?_⟩⟩
      · have hs1 : c1 < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
        have hs2 : c2 < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
        have hs3 : b1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
        have hadd := matrixIntegral_add (hb1 Φ ⟨x, hx⟩ s hs3) (hb1 Φ ⟨y, hy⟩ s hs3)
        simp only [Padic.matrixIntegral] at hc1 hc2 ⊢
        rw [hadd, hc1 s hs1, hc2 s hs2, Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
      · have hs1 : d1 < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
        have hs2 : d2 < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
        have hs3 : b2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
        have hadd := matrixIntegral_add (hb2 (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ)
          ⟨x, hx⟩ s hs3) (hb2 (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ) ⟨y, hy⟩ s hs3)
        have hι : coefficientIota (x + y) = coefficientIota x + coefficientIota y := rfl
        simp only [Padic.matrixIntegral] at hd1 hd2 ⊢
        rw [hι, hadd, hd1 s hs1, hd2 s hs2, Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
    | smul r x hx ih =>
      obtain ⟨M, Ψ0, Ψ1, f0, f1, ⟨c1, hc1⟩, ⟨d1, hd1⟩⟩ := ih
      refine ⟨M, Ψ0, Ψ1, fun j => r • f0 j, f1, ⟨c1, fun s hs => ?_⟩, ⟨d1, fun s hs => ?_⟩⟩
      · simp only [Padic.matrixIntegral] at hc1 ⊢
        rw [matrixIntegral_smul, hc1 s hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul, matrixIntegral_smul, mul_assoc]
      · have hι : ∀ z : Langlands.GeneralLinear (t + 1) F.Carrier → ℂ,
            coefficientIota (r • z) = r • coefficientIota z := fun _ => rfl
        have hι0 : ∀ z : Langlands.GeneralLinear (m 0 + 1) F.Carrier → ℂ,
            coefficientIota (r • z) = r • coefficientIota z := fun _ => rfl
        simp only [Padic.matrixIntegral] at hd1 ⊢
        rw [hι, matrixIntegral_smul, hd1 s hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul, hι0, matrixIntegral_smul, mul_assoc]
  obtain ⟨M, Ψ0, Ψ1, f0, f1, hZ, hZD⟩ := hspan f.val f.property
  have hq : 1 < F.canonicalTopologicalData.residueCardinality :=
    F.canonicalTopologicalData.residueCardinality_gt_one
  choose R0 hR0 using fun j => (hdata 0).1.2.1 (Ψ0 j) (f0 j)
  choose R1 hR1 using fun j => (hdata 1).1.2.1 (Ψ1 j) (f1 j)
  choose RD0 hRD0 using fun j =>
    (hdata 0).2.1.2.1 (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ0 j)) (f0 j)
  choose RD1 hRD1 using fun j =>
    (hdata 1).2.1.2.1 (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ1 j)) (f1 j)
  have hFE0 : ∀ j, NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
      (P 0) (PD 0) 1 (c 0) 0 (a 0) (R0 j) (RD0 j) := by
    intro j
    obtain ⟨Ψhat, hpair, hfe⟩ := (hdata 0).2.2 (Ψ0 j)
    have hhat : Ψhat = rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ0 j) :=
      Hecke.TestFunction.ext fun x => by rw [(hpair x).2, rectangularFourierEquiv_apply]
    subst hhat
    exact hfe (f0 j) (R0 j) (RD0 j) (hR0 j) (hRD0 j)
  have hFE1 : ∀ j, NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
      (P 1) (PD 1) 1 (c 1) 0 (a 1) (R1 j) (RD1 j) := by
    intro j
    obtain ⟨Ψhat, hpair, hfe⟩ := (hdata 1).2.2 (Ψ1 j)
    have hhat : Ψhat = rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ1 j) :=
      Hecke.TestFunction.ext fun x => by rw [(hpair x).2, rectangularFourierEquiv_apply]
    subst hhat
    exact hfe (f1 j) (R1 j) (RD1 j) (hR1 j) (hRD1 j)
  simp only [Fin.prod_univ_two, Fin.sum_univ_two]
  exact normalizedFunctionalEquation_of_eventually_sum_mul hq Finset.univ hR.2 hRD.2
    (fun j s => Padic.matrixIntegral F (Ψ0 j) (s + jpssShift (m 0)) (f0 j).val)
    (fun j s => Padic.matrixIntegral F (Ψ1 j) (s + jpssShift (m 1)) (f1 j).val)
    (fun j s => Padic.matrixIntegral F
      (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ0 j))
      (s + jpssShift (m 0)) (coefficientIota (f0 j).val))
    (fun j s => Padic.matrixIntegral F
      (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ1 j))
      (s + jpssShift (m 1)) (coefficientIota (f1 j).val))
    R0 R1 RD0 RD1 hZ hZD (fun j _ => (hR0 j).2) (fun j _ => (hR1 j).2)
    (fun j _ => (hRD0 j).2) (fun j _ => (hRD1 j).2) (fun j _ => hFE0 j) (fun j _ => hFE1 j)

end Langlands.GodementJacquet
