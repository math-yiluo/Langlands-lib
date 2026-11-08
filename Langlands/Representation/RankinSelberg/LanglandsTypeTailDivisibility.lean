import Langlands.Representation.RankinSelberg.LanglandsTypeLPolynomialData
import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.RankinSelberg.InducedTailLFactorProof
import Langlands.Representation.Classification.LanglandsHeadTailStandardModule
import Langlands.Representation.Induction.HeterogeneousConstruction

/-! Tail divisibility on genuine standard modules at their actual ranks. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)

/-- Full Whittaker type at any positive rank; the rank-zero case is false. -/
def IsOfPadicRankWhittakerType {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V) : Prop :=
  match n, π with
  | r + 1, π => letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π
  | 0, _ => False

variable {F ψ}

/-- Actual representation equivalence preserves full type at every rank. -/
theorem IsOfPadicRankWhittakerType.of_equiv
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear n F.Carrier) W}
    (hπ : IsOfPadicRankWhittakerType F ψ π) (e : π.Equiv σ) :
    IsOfPadicRankWhittakerType F ψ σ := by
  cases n with
  | zero => exact hπ.elim
  | succ n =>
    let := F.canonicalTopologicalData.topology
    exact IsOfWhittakerType.of_equiv hπ e

variable (F ψ)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

set_option maxHeartbeats 800000 in
/-- Closed tail divisibility for an arbitrary actual two-block shape and any
already certified polynomials. The literal carrier lifts are removed through
actual representation equivalences. -/
theorem twoBlockShapeTailLPolynomial_dvd {n t : ℕ}
    (B : BlockShape n) (hB : B.length = 2)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (Langlands.GeneralLinear (B.size i) F.Carrier) (V i))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hπ : ∀ i, IsOfPadicRankWhittakerType F ψ (π i))
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ)
    {P Ptail : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (F.canonicalNormalizedProductInduced B π) σ P)
    (htail : IsPadicRankLPolynomial F ψ ν.val
      (π (Fin.cast hB.symm (1 : Fin 2))) σ Ptail) : Ptail ∣ P := by
  let := F.canonicalTopologicalData.topology
  rcases B with ⟨k, size, pos, total⟩
  dsimp at hB
  subst k
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, size = ![a + 1, b + 1] := by
    refine ⟨size 0 - 1, size 1 - 1, ?_⟩
    funext i
    fin_cases i <;> simp [Nat.sub_add_cancel (pos _)]
  have htotal : (a + 1) + (b + 1) = n := by simpa using total
  subst n
  obtain ⟨Pfull, Qtail, hfull, hQtail, hdiv⟩ :=
    inducedTailLFactor p F ψ ν a b t (π 0) (π 1) σ (hπ 0) (hπ 1) hσ
  let e := F.heterogeneousPairToPairEquiv (Nat.succ_pos a) (Nat.succ_pos b)
    (Representation.Equiv.refl (π 0)) (Representation.Equiv.refl (π 1))
  have hfull' := (IsPadicSymmetricLPolynomial.congr_equiv e
    (Representation.Equiv.refl σ)).mp hfull
  let f := F.canonicalTopologicalData.normalizedProductInducedEquiv
    (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
    (σ := π) (τ := Shahidi.pairFamily (π 0) (π 1))
    (Fin.cases (Representation.Equiv.refl (π 0))
      (Fin.cases (Representation.Equiv.refl (π 1)) (fun i => i.elim0)))
  have hP' := (IsPadicRankLPolynomial.congr_equiv f
    (Representation.Equiv.refl σ)).mp hP
  have heq : P = Pfull := hP'.unique hfull'
  have hteq : Ptail = Qtail := htail.unique hQtail
  simpa only [heq, hteq] using hdiv

/-- Real twists of analytic tempered actions have full type at positive rank. -/
theorem analyticTemperedRealTwistRankWhittakerType {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (hi : Representation.IsIrreducible π)
    (ht : F.canonicalTopologicalData.IsTempered π) (s : ℝ) :
    IsOfPadicRankWhittakerType F ψ
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π) := by
  cases n with
  | zero => omega
  | succ n => exact analyticTemperedRealTwistWhittakerType F ψ π hi ht s

/-- Each original twisted block has full type at its actual positive rank. -/
theorem langlandsTwistedBlockRankWhittakerType {n : ℕ}
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData n)
    (i : Fin d.shape.length) :
    letI := F.canonicalTopologicalData.topology;
    IsOfPadicRankWhittakerType F ψ
      (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation := by
  let := F.canonicalTopologicalData.topology
  exact analyticTemperedRealTwistRankWhittakerType F ψ (d.shape.positive i)
    (d.blocks i).representation (d.irreducible i) (d.tempered i) (d.exponent i)

/-- A genuine positive-rank standard module has full type at its actual rank. -/
theorem langlandsStandardModuleRankWhittakerType {n : ℕ} (hn : 0 < n)
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData n) :
    letI := F.canonicalTopologicalData.topology;
    IsOfPadicRankWhittakerType F ψ d.standardModule.representation := by
  cases n with
  | zero => omega
  | succ n => exact langlandsStandardModuleWhittakerType F ψ d

/-- The certified polynomial of the genuine tail against a full-type test
representation divides the certified polynomial of the original standard. -/
theorem langlandsStandardTailLPolynomial_dvd {r t k : ℕ}
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData (r + 1))
    (h : d.shape.length = k + 2)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ)
    {P Ptail : ℂ[X]}
    (hP : letI := F.canonicalTopologicalData.topology;
      IsPadicSymmetricLPolynomial F ψ ν.val d.standardModule.representation σ P)
    (htail : letI := F.canonicalTopologicalData.topology;
      IsPadicRankLPolynomial F ψ ν.val (d.tail h).standardModule.representation σ Ptail) :
    Ptail ∣ P := by
  let := F.canonicalTopologicalData.topology
  have ht := langlandsStandardModuleRankWhittakerType F ψ
    (d.shape.tailRank_pos h) (d.tail h)
  have hf : ∀ i, IsOfPadicRankWhittakerType F ψ
      (d.headTailStandardFactors h i).representation := by
    intro i
    fin_cases i
    · have hd := langlandsTwistedBlockRankWhittakerType F ψ d (d.shape.headIndex h)
      have E := SmoothRep.universeLiftEquiv.{uF}
        (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent (d.shape.headIndex h))
      exact hd.of_equiv E
    · exact ht
  exact twoBlockShapeTailLPolynomial_dvd F ψ ν (d.shape.headTailShape h) rfl
    (fun i => (d.headTailStandardFactors h i).representation) σ hf hσ
    ((IsPadicSymmetricLPolynomial.congr_equiv (d.headTailStandardModuleEquiv h)
      (Representation.Equiv.refl σ)).mp hP) htail

end Langlands.RankinSelberg
