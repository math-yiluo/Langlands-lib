import Langlands.Correspondence.SegmentGaloisGamma
import Langlands.Correspondence.SegmentHeadGammaExpression
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal
import Langlands.Correspondence.AssemblyEpsilonRemainingReduction
import Langlands.Correspondence.AssemblyBlockPairEuler

/-!
# Segment-pair epsilon inheritance from the segment-head factor formulas

For a supercuspidal correspondence `c0` and a local-constant system for which
`c0` is compatible with pair factors, the epsilon factor of a pair of segment
heads `Q(Δ)`, `Q(Δ')`, `Δ = [c0 σ, …, ν^a c0 σ]`, `Δ' = [c0 τ, …, ν^b c0 τ]`, is the
arithmetic epsilon factor of the uncentered blocks `σ ⊗ Sp(a + 1)` and
`τ ⊗ Sp(b + 1)`. The premises are the segment-head L- and gamma-factor formulas
of Henniart 2002, §2.6, the block-pair gamma law of Henniart 2002, §2.4, and the
arithmetic block-pair L-factor formula; none of them is proved here.

The gamma factor of the segment heads is `ε_Q · P_Q / P_Q^∨(δ/X)` and, by the
segment-head gamma formula and the twisted supercuspidal gamma factors, also
`∏_i ∏_j ε_(i+j) LR(ω^(i+j) σ ⊗ τ)`. The block-pair gamma law rewrites the latter
as `ε_T · LR(T)` with `ε_T` the arithmetic epsilon monomial of the blocks, and the
L-factor formulas identify the L-polynomials. Since both dual polynomials have
constant term `1`, the two epsilon monomials agree.
-/

noncomputable section

universe uF uP uA

open Polynomial

namespace Langlands.Correspondence

open PadicField.TopologicalData

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
  LocalFactor.CommonClosureGamma LocalFactor.PairBlock

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance segmentEpsilonFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance segmentEpsilonGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- **Twisted supercuspidal gamma factors.** For a supercuspidal correspondence
`c0` compatible with pair factors for the system, supercuspidal representatives
`A`, `A'` of `c0 σ`, `c0 τ` and `k : ℕ`, some `c q^(-ms)` is the arithmetic epsilon
factor of `ω^k B ⊗ B'`, and `c X^m LR(ω^k B ⊗ B')` is the gamma factor of
`(ν^k A, A')` for the self-dual `ν`. -/
theorem IsSupercuspidalCorrespondence.exists_twistedPairGamma
    {c0 : SupercuspidalMap.{uF, uP, uA} F} (hc0 : IsSupercuspidalCorrespondence F c0)
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε}
    (hcompat : SupercuspidalPairFactorCompatibility F eC ε hε c0)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hνψ : IsSelfDualMeasure F ψ ν) {d t : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
    (τ : IrreducibleWeilClass.{uF, uP} F t.succPNat)
    (B B' : LocalWeilRepresentation.{uF, uP} F)
    (hσ : FiniteRepresentation.classOf B = weilClassForget F σ)
    (hτ : FiniteRepresentation.classOf B' = weilClassForget F τ)
    (A : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := d + 1))
    (A' : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := t + 1))
    (hA : A.isoClass = c0 d.succPNat σ) (hA' : A'.isoClass = c0 t.succPNat τ) (k : ℕ) :
    ∃ e : ℂˣ × ℤ,
      IsArithmeticPairEpsilonFactor F eC ε hε ψ
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
          (localNormCharacter F).toMonoidHom
          (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ k) B)))
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
          (localNormCharacter F).toMonoidHom B')) e.1 e.2 ∧
      RankinSelberg.IsPadicSymmetricGammaFactor F ψ ν
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (d + 1)) (k : ℝ)
          A.obj.representation) A'.obj.representation
        ((RankinSelberg.rationalEpsilonMonomial e.1 e.2 : RatFunc ℂ) *
          WeilDeligne.rationalLRatio (localTwistTensor F B B' k) (localInertia F)
            (localGeometricFrobenius F) (residueReflection F)) := by
  obtain ⟨_, hdual, e, he, _, _, htw, _⟩ := hc0
  set χ := normPowerQuasiCharacter F e k with hχdef
  have hdet := determinantQuasiCharacter_normPowerQuasiCharacter F he k d.succPNat
  have hopen : IsOpen ((determinantQuasiCharacter F d.succPNat χ).ker :
      Set (GeneralLinear (d.succPNat : ℕ) F.Carrier)) := by
    rw [hdet]
    exact F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter _ _
  set σ' := FiniteRepresentation.continuousIrreducibleTwistEquiv
    (LocalFactor.RankOne.weilCharacter F e χ) (d.succPNat : ℕ) σ with hσ'def
  have hc : c0 d.succPNat σ' = (GeneralLinear.SupercuspidalRep.twist
      (determinantQuasiCharacter F d.succPNat χ) hopen
      (GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom) A).isoClass := by
    have h := (isSupercuspidalCharacterTwist_iff_eq_twist F χ hopen _ _).mp (htw _ σ χ)
    rw [← hA] at h
    exact h
  obtain ⟨-, hG⟩ := supercuspidalGammaFromFactors F eC ε hε c0 hcompat hdual ψ d t σ' τ
  obtain ⟨G, hGrep, c, m, hcm, hGeq⟩ := hG ν hνψ
  rw [hc, ← hA'] at hGrep
  change RankinSelberg.IsPadicSymmetricGammaFactor F ψ ν
    (Langlands.twist (determinantQuasiCharacter F d.succPNat χ) A.obj.representation)
    A'.obj.representation G at hGrep
  rw [hdet] at hGrep
  have hpow : (LocalFactor.RankOne.weilCharacter F e χ).toMonoidHom =
      (localNormCharacter F).toMonoidHom ^ k := by
    rw [hχdef, weilCharacter_normPowerQuasiCharacter]
    refine MonoidHom.ext fun w => ?_
    rw [MonoidHom.pow_apply]
    exact ContinuousMonoidHom.pow_apply _ _ _
  have hσ' : FiniteRepresentation.classOf (FiniteRepresentation.twist
      ((localNormCharacter F).toMonoidHom ^ k) B) = weilClassForget F σ' := by
    rw [hσ'def, weilClassForget, FiniteRepresentation.forget_continuousIrreducibleTwistEquiv,
      ← weilClassForget, ← hσ, FiniteRepresentation.twistClass_classOf, hpow]
  rw [weilPairClass_eq_classOf F σ' _ hσ', weilPairClass_eq_classOf F τ B' hτ] at hcm hGeq
  refine ⟨(c, m), hcm, ?_⟩
  rw [hGeq] at hGrep
  exact hGrep

/-- **Segment-pair epsilon compatibility.** From the segment-head L- and gamma
formulas of Henniart 2002, §2.6 (carriers in `uA`), the block-pair gamma law of
Henniart 2002, §2.4 and the arithmetic block-pair L-factor formula: for every
supercuspidal correspondence `c0` compatible with pair factors for the system,
the epsilon factor of every pair of segment-head models is the arithmetic
epsilon factor of the corresponding pair of uncentered blocks. -/
theorem segmentPairEpsilonCompatibility_of_segmentHeads
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hG : RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA})
    (hBPG : BlockPairGamma.{uF, uP} F) (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} (hc0 : IsSupercuspidalCorrespondence F c0)
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε}
    (hcompat : SupercuspidalPairFactorCompatibility F eC ε hε c0) :
    SegmentPairEpsilonCompatibility F eC ε hε c0 := by
  intro ψ ν hνψ d a t b σ τ B B' hσ hτ n n' Q Q' hQ hQ'
  -- L-polynomials (Henniart 2.6 and the arithmetic block formula)
  obtain ⟨PL, hPL, hLT⟩ := segmentPairLCompatibility_of_segmentHeads F hL hB
    (hc0.twistedSupercuspidalPairLCompatibility F) ψ ν hνψ σ τ B B' hσ hτ Q Q' hQ hQ'
  obtain ⟨hn, P0, hP0, ⟨eQ⟩⟩ := hQ
  obtain ⟨hn', P0', hP0', ⟨eQ'⟩⟩ := hQ'
  subst hn hn'
  obtain ⟨A, hA, hhead⟩ := hP0
  obtain ⟨A', hA', hhead'⟩ := hP0'
  -- the gamma factor of the segment heads
  obtain ⟨e, P, D, H, he, hP, hD, hH, hγ⟩ := RankinSelberg.exists_segmentHead_rationalGammaExpression
    F hG ψ ⟨ν, hνψ⟩ _ _ P0 P0' A A' ⟨A, hA, hhead⟩ ⟨A', hA', hhead'⟩ hA hA'
  have hPPL : P = PL := RankinSelberg.IsPadicRankLPolynomial.unique hP
    ((isPadicRankLPolynomial_congr_equiv F eQ eQ').mp hPL)
  have hET : WeilDeligne.eulerPolynomial (localBlockTensor F B B' a b) (localInertia F)
      (localGeometricFrobenius F) = P := by
    rw [hPPL]
    apply RatFunc.algebraMap_injective ℂ
    exact inv_injective hLT
  have hP0ne : P ≠ 0 := by
    rw [← hET]
    intro h0
    have h1 := WeilDeligne.eulerPolynomial_coeff_zero (localBlockTensor F B B' a b)
      (localInertia F) (localGeometricFrobenius F)
    rw [h0, Polynomial.coeff_zero] at h1
    exact zero_ne_one h1
  -- twisted supercuspidal gamma factors
  choose ek hek hγk using fun k : ℕ =>
    IsSupercuspidalCorrespondence.exists_twistedPairGamma F hc0 hcompat ψ ν hνψ σ τ B B' hσ hτ
      A A' hA hA' k
  have hHk : ∀ (i : Fin (a + 1)) (j : Fin (b + 1)), H i j =
      (RankinSelberg.rationalEpsilonMonomial (ek (i.val + j.val)).1 (ek (i.val + j.val)).2 :
        RatFunc ℂ) *
        WeilDeligne.rationalLRatio (localTwistTensor F B B' (i.val + j.val)) (localInertia F)
          (localGeometricFrobenius F) (residueReflection F) := fun i j =>
    (hH i j).unique (RankinSelberg.isPadicRankGammaFactor_succ.mpr (hγk (i.val + j.val)))
  have hBc := isContinuous_of_classOf_eq F hσ
  have hB'c := isContinuous_of_classOf_eq F hτ
  refine ⟨e, (RankinSelberg.IsPadicRankEpsilonFactor.congr_equiv eQ.symm eQ'.symm).mp he, ?_⟩
  obtain ⟨⟨ψ₀, μ₀, -, -, ⟨hψ₀, hμ₀, -, -⟩, -, -⟩, hΦ, -⟩ := hek 0
  refine ⟨⟨ψ₀, μ₀, _, _, ⟨hψ₀, hμ₀, ⟨_, rfl, ⟨restrictBlockBaseEquiv F B (a + 1)⟩⟩,
    ⟨_, rfl, ⟨restrictBlockBaseEquiv F B' (b + 1)⟩⟩⟩,
    block_isContinuous F _ _ (baseLift_isContinuous F hBc) (a + 1),
    block_isContinuous F _ _ (baseLift_isContinuous F hB'c) (b + 1)⟩, hΦ, ?_⟩
  rintro ψ' μ X Y ⟨hψ', hμ, hX, hY⟩ hXc hYc Φ s
  obtain ⟨x⟩ := IsBaseRestriction.nonempty_equiv F rfl hX
  obtain ⟨y⟩ := IsBaseRestriction.nonempty_equiv F rfl hY
  set e' : Fin (a + 1) → Fin (b + 1) → ℂˣ × ℤ := fun i j => ek (i.val + j.val) with he'def
  rw [conditionalPairEpsilonValue_eq_of_equiv F eC ε hε _ ψ' μ hXc
      (block_isContinuous F _ _ (baseLift_isContinuous F hBc) (a + 1)) hYc
      (block_isContinuous F _ _ (baseLift_isContinuous F hB'c) (b + 1))
      (x.symm.trans (restrictBlockBaseEquiv F B (a + 1)))
      (y.symm.trans (restrictBlockBaseEquiv F B' (b + 1))) Φ s,
    conditionalPairEpsilonValue_baseBlock F eC ε hε ψ' μ B B' hBc hB'c a b Φ s e'
      (fun i j => (hek (i.val + j.val)).2.2 ψ' μ _ _
        ⟨hψ', hμ, ⟨_, rfl, ⟨restrictTwistedBaseEquiv F B (i.val + j.val)⟩⟩,
          ⟨_, rfl, ⟨restrictZeroBaseEquiv F B'⟩⟩⟩ _ _ Φ s)]
  -- cancellation of the two gamma expressions
  have hGR := rationalLRatio_localBlockTensor F hBPG eC ε hε ψ' μ B B' hBc hB'c a b Φ
  have hprod : ∏ i, ∏ j, H i j = RankinSelberg.rationalGammaExpression (residueReflection F)
      ((RankinSelberg.epsilonFactorProduct e').1 *
        WeilDeligne.quotientConstantCorrection (baseBlockTensor F B B' a b)
          (inertia F (baseExtension F)) Φ.val)
      ((RankinSelberg.epsilonFactorProduct e').2 +
        WeilDeligne.conductorCorrection (baseBlockTensor F B B' a b)
          (inertia F (baseExtension F))) P
      (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual (localBlockTensor F B B' a b))
        (localInertia F) (localGeometricFrobenius F)) := by
    change ∏ i : Fin (a + 1), ∏ j : Fin (b + 1), H i j = _
    simp only [hHk, Finset.prod_mul_distrib]
    rw [← hGR, show (∏ i : Fin (a + 1), ∏ j : Fin (b + 1),
        (RankinSelberg.rationalEpsilonMonomial (ek (i.val + j.val)).1
          (ek (i.val + j.val)).2 : RatFunc ℂ)) =
        ∏ i, ∏ j, (RankinSelberg.rationalEpsilonMonomial (e' i j).1 (e' i j).2 : RatFunc ℂ)
        from rfl, RankinSelberg.prod_rationalEpsilonMonomial e',
      RankinSelberg.rationalGammaExpression, WeilDeligne.rationalLRatio_eq, hET,
      RankinSelberg.coe_rationalEpsilonMonomial, RankinSelberg.coe_rationalEpsilonMonomial]
    simp only [RatFunc.algebraMap_eq_C, Units.val_mul, map_mul]
    rw [zpow_add₀ RatFunc.X_ne_zero, zpow_natCast]
    ring
  obtain ⟨h1, h2⟩ := RankinSelberg.rationalGammaExpression_cancel hP0ne hD
    (WeilDeligne.eulerPolynomial_coeff_zero _ _ _) (hγ.trans hprod)
  rw [h1, h2]

/-- **Segment-level epsilon inheritance** from the segment-head L- and gamma
formulas of Henniart 2002, §2.6, the block-pair gamma law of Henniart 2002, §2.4
and the arithmetic block-pair L-factor formula. -/
theorem supercuspidalSegmentPairInheritance_of_segmentHeads
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hG : RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA})
    (hBPG : BlockPairGamma.{uF, uP} F) (hB : ArithmeticBlockPairLFactor.{uF, uP} F) :
    SupercuspidalSegmentPairInheritance.{uF, uP, uA} F :=
  fun _ _ _ _ hc0 hcompat =>
    segmentPairEpsilonCompatibility_of_segmentHeads F hL hG hBPG hB hc0 hcompat

/-- Segment-level epsilon inheritance with the arithmetic block-pair L-factor
formula replaced by the Weil-Deligne Euler-factor formula for block pairs. -/
theorem supercuspidalSegmentPairInheritance_of_segmentHeads_of_wdEuler
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hG : RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA})
    (hBPG : BlockPairGamma.{uF, uP} F) (hE : WDEulerPairBlockStatement.{0, uF, uP, uP}) :
    SupercuspidalSegmentPairInheritance.{uF, uP, uA} F :=
  supercuspidalSegmentPairInheritance_of_segmentHeads F hL hG hBPG
    (arithmeticBlockPairLFactor_of_wdEulerPairBlock F hE)

/-- The segment-level epsilon reduction: the segment-head L- and gamma formulas of
Henniart 2002, §2.6 (carriers in `uA`), the block-pair gamma law of Henniart 2002,
§2.4 and the Weil-Deligne Euler-factor formula for block pairs together imply
segment-level epsilon inheritance. -/
def SegmentEpsilonReductionStatement : Prop :=
  RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA} →
    RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA} →
      BlockPairGamma.{uF, uP} F → WDEulerPairBlockStatement.{0, uF, uP, uP} →
        SupercuspidalSegmentPairInheritance.{uF, uP, uA} F

/-- The segment-level epsilon reduction holds. -/
theorem segmentEpsilonReduction : SegmentEpsilonReductionStatement.{uF, uP, uA} F :=
  fun hL hG hBPG hE => supercuspidalSegmentPairInheritance_of_segmentHeads_of_wdEuler F hL hG hBPG hE

/-- **Assembled epsilon inheritance** from multisegment datum matching, the
segment-head L- and gamma formulas of Henniart 2002, §2.6, the block-pair gamma
law of Henniart 2002, §2.4 and the Weil-Deligne Euler-factor formula for block
pairs. None of these premises is proved here. -/
theorem assemblyEpsilonInheritance_of_segmentHeads
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hG : RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA})
    (hBPG : BlockPairGamma.{uF, uP} F) (hE : WDEulerPairBlockStatement.{0, uF, uP, uP}) :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_datumMatching_and_segmentPairs F hP
    (supercuspidalSegmentPairInheritance_of_segmentHeads_of_wdEuler F hL hG hBPG hE)

end Langlands.Correspondence
