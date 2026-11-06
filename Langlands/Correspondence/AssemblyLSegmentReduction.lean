import Langlands.Correspondence.AssemblyLReduction
import Langlands.Representation.RankinSelberg.SegmentFactorStatement

/-!
# Reduction of segment-pair L compatibility to supercuspidal pairs

Segment-pair L compatibility of a supercuspidal map `c0` follows from three
explicit premises: the L-factor formula of Henniart 2002, §2.6 for pairs of
segment heads (`SegmentHeadLFactorStatement`), the corresponding product formula
for arithmetic L-factors of pairs of uncentered special blocks, and the
compatibility of `c0` with pair L-factors after twisting the first factor by
`ν^x`, `x ∈ ℕ`. None of the three premises is proved here.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Polynomial PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyLSegmentFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyLSegmentGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Arithmetic L-factors of pairs of uncentered special blocks: with `ω` the norm
character of the Weil group,
`L(s, (B ⊗ Sp(a + 1)) ⊗ (B' ⊗ Sp(b + 1))) = ∏_j L(s, ω^(a+b-j) B ⊗ B')`,
`0 ≤ j < min(a + 1, b + 1)`, the factors on the right having zero monodromy. -/
def ArithmeticBlockPairLFactor : Prop :=
  ∀ (B B' : Weil.Local.LocalWeilRepresentation.{uF, uP} F) (a b : ℕ),
    arithmeticPairLFactor F
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
          (Weil.Local.localNormCharacter F).toMonoidHom B (a + 1)))
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
          (Weil.Local.localNormCharacter F).toMonoidHom B' (b + 1))) =
      ∏ j : Fin (min (a + 1) (b + 1)), arithmeticPairLFactor F
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
          (Weil.Local.localNormCharacter F).toMonoidHom
          (FiniteRepresentation.twist
            ((Weil.Local.localNormCharacter F).toMonoidHom ^ (a + b - (j : ℕ))) B)))
        (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
          (Weil.Local.localNormCharacter F).toMonoidHom B'))

/-- Pair L compatibility of `c0` after twisting the first factor by `ν^x`: for
irreducible Weil classes `σ`, `τ` with representatives `B`, `B'`, supercuspidal
representatives `A`, `A'` of `c0 σ`, `c0 τ`, and `x : ℕ`, one polynomial `P` is the
pair L-polynomial of `(ν^x A, A')` for the self-dual `ν`, and `1 / P(q^(-s))` is the
arithmetic L-factor of `ω^x B ⊗ B'`. -/
def TwistedSupercuspidalPairLCompatibility (c0 : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
    ∀ {d t : ℕ} (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
      (τ : IrreducibleWeilClass.{uF, uP} F t.succPNat)
      (B B' : Weil.Local.LocalWeilRepresentation.{uF, uP} F),
      FiniteRepresentation.classOf B = weilClassForget F σ →
      FiniteRepresentation.classOf B' = weilClassForget F τ →
      ∀ (A : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := d + 1))
        (A' : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := t + 1)),
        A.isoClass = c0 d.succPNat σ → A'.isoClass = c0 t.succPNat τ →
        ∀ x : ℕ, ∃ P : ℂ[X],
          RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
            (realPowerTwist (F.canonicalTopologicalData.determinantNorm (d + 1)) (x : ℝ)
              A.obj.representation) A'.obj.representation P ∧
          arithmeticPairLFactor F
              (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
                (Weil.Local.localNormCharacter F).toMonoidHom
                (FiniteRepresentation.twist
                  ((Weil.Local.localNormCharacter F).toMonoidHom ^ x) B)))
              (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy
                (Weil.Local.localNormCharacter F).toMonoidHom B')) =
            (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹

/-- The arbitrary-rank L relation is invariant under representation equivalences. -/
theorem isPadicRankLPolynomial_congr_equiv
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier} {ν : LocalAdditiveHaarMeasure F}
    {n t : ℕ} {V W V₂ W₂ : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear t F.Carrier) W}
    {π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂}
    {σ₂ : Representation ℂ (GeneralLinear t F.Carrier) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {P : ℂ[X]} :
    RankinSelberg.IsPadicRankLPolynomial F ψ ν π σ P ↔
      RankinSelberg.IsPadicRankLPolynomial F ψ ν π₂ σ₂ P := by
  match n, t, π, σ, π₂, σ₂, φ, φ' with
  | _ + 1, _ + 1, _, _, _, _, φ, φ' =>
    exact RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv φ φ'
  | 0, _, _, _, _, _, _, _ => exact Iff.rfl
  | _ + 1, 0, _, _, _, _, _, _ => exact Iff.rfl

/-- Segment-pair L compatibility from the segment-head L formula of Henniart 2002,
§2.6, the arithmetic block-pair formula and twisted supercuspidal compatibility. -/
theorem segmentPairLCompatibility_of_segmentHeads
    {c0 : SupercuspidalMap.{uF, uP, uA} F}
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : TwistedSupercuspidalPairLCompatibility F c0) :
    SegmentPairLCompatibility F c0 := by
  intro ψ ν hνψ d a t b σ τ B B' hσ hτ n n' Q Q' hQ hQ'
  obtain ⟨hn, P0, hP0, ⟨e⟩⟩ := hQ
  obtain ⟨hn', P0', hP0', ⟨e'⟩⟩ := hQ'
  subst hn hn'
  obtain ⟨A, hA, hhead⟩ := hP0
  obtain ⟨A', hA', hhead'⟩ := hP0'
  obtain ⟨P, R, hP, hR, hPR⟩ :=
    hH p F ψ ⟨ν, hνψ⟩ _ _ P0 P0' A A' ⟨A, hA, hhead⟩ ⟨A', hA', hhead'⟩ hA hA'
  refine ⟨P, (isPadicRankLPolynomial_congr_equiv F e.symm e'.symm).mp hP, ?_⟩
  rw [hB, hPR, map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨Pj, hPj, hLj⟩ := hT ψ ν hνψ σ τ B B' hσ hτ A A' hA hA' (a + b - (j : ℕ))
  have hj : (j : ℕ) < min (a + 1) (b + 1) := j.isLt
  have hx : ((a + b - (j : ℕ) : ℕ) : ℝ) =
      ((a + 1 : ℕ) : ℝ) + ((b + 1 : ℕ) : ℝ) - 2 - ((j : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hx] at hPj
  rw [hLj, RankinSelberg.IsPadicRankLPolynomial.unique
    (RankinSelberg.isPadicRankLPolynomial_succ.mpr hPj) (hR j)]

/-- Twisted supercuspidal L inheritance: every supercuspidal correspondence is
compatible with pair L-factors after twisting the first factor by `ν^x`. -/
def SupercuspidalTwistedPairLInheritance : Prop :=
  ∀ c0 : SupercuspidalMap.{uF, uP, uA} F,
    IsSupercuspidalCorrespondence F c0 → TwistedSupercuspidalPairLCompatibility F c0

/-- Segment-level L inheritance from the segment-head L formula, the arithmetic
block-pair formula and twisted supercuspidal L inheritance. -/
theorem supercuspidalSegmentPairLInheritance_of_segmentHeads
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F) :
    SupercuspidalSegmentPairLInheritance.{uF, uP, uA} F :=
  fun c0 hc0 => segmentPairLCompatibility_of_segmentHeads F hH hB (hT c0 hc0)

/-- Pair L-factor inheritance of the assembly from multisegment datum existence,
JPSS (9.5) in product form, arithmetic multiplicativity, the segment-head L
formula of Henniart 2002, §2.6, the arithmetic block-pair formula and twisted
supercuspidal L inheritance. -/
theorem assemblyLInheritance_of_segmentHeads
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F)
    (hT : SupercuspidalTwistedPairLInheritance.{uF, uP, uA} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F :=
  assemblyLInheritance_of_segmentPairs F hP hJ hD
    (supercuspidalSegmentPairLInheritance_of_segmentHeads F hH hB hT)

end Langlands.Correspondence
