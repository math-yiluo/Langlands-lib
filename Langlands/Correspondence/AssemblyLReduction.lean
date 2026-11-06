import Langlands.Correspondence.AssemblyLFactorStatement
import Langlands.Correspondence.AssemblyEpsilonReduction
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement

/-!
# Reduction of assembled L inheritance to segment pairs

Pair L-factor compatibility of an assembled full map follows from four explicit
premises: Langlands heads of multisegments have square-integrable data whose blocks
are segment heads, JPSS (9.5) in product form, arithmetic pair L-factors are
multiplicative on direct sums of Weil–Deligne representations, and segment heads
of the segments `[c0 σ, …, ν^a c0 σ]` have the L-factors of the blocks
`σ ⊗ Sp(a + 1)`. None of the four premises is proved here.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Polynomial PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyLFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyLGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Square-integrable Langlands data of multisegment heads, with blocks in the
universe `uA`: if `J` is the Langlands head of the multisegment `{Δ_1, …, Δ_r}`,
then `J` is a Langlands quotient of some such datum whose blocks are, after a
permutation `φ`, models of the segment heads `Q(Δ_(φ k))`. -/
def MultisegmentHeadDatumExistence : Prop :=
  ∀ (r : ℕ) (Δ : Fin r → Segment.{uA, uF} F.canonicalTopologicalData) {n : ℕ}
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier)),
    Multisegment.IsLanglandsHead
        (List.ofFn Δ : Multisegment.{uA, uF} F.canonicalTopologicalData) J →
      ∃ d : SquareIntegrableLanglandsDatum.{uA, uF} F.canonicalTopologicalData n,
        d.IsLanglandsQuotient J ∧
          ∃ φ : Fin d.shape.length ≃ Fin r, ∀ k, IsSegmentHeadModel F (Δ (φ k)) (d.blocks k)

/-- Datum matching for every presenting datum gives a matching presenting datum. -/
theorem MultisegmentHeadDatumMatching.datumExistence
    (h : MultisegmentHeadDatumMatching.{uF, uA} F) :
    MultisegmentHeadDatumExistence.{uF, uA} F := by
  intro r Δ n J hJ
  obtain ⟨⟨d, hd⟩, hall⟩ := h r Δ J hJ
  exact ⟨d, hd, hall d hd⟩

/-- Multiplicativity of arithmetic pair L-factors: if `A ≅ ⊕_i B_i` and
`A' ≅ ⊕_j B'_j`, then `L(s, A ⊗ A') = ∏_(i,j) L(s, B_i ⊗ B'_j)`. -/
def ArithmeticPairLDirectSum : Prop :=
  ∀ {r t : ℕ} (B : Fin r → Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
    (B' : Fin t → Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
    (A A' : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F),
    Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A) →
    Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B') A') →
    arithmeticPairLFactor F (WeilDeligneRepresentation.classOf A)
        (WeilDeligneRepresentation.classOf A') =
      ∏ i, ∏ j, arithmeticPairLFactor F (WeilDeligneRepresentation.classOf (B i))
        (WeilDeligneRepresentation.classOf (B' j))

/-- Segment-pair L compatibility of `c0`: for irreducible Weil classes `σ`, `τ`
with representatives `B`, `B'`, and models `Q`, `Q'` of the heads of the segments
`[c0 σ, …, ν^a c0 σ]` and `[c0 τ, …, ν^b c0 τ]`, one polynomial `P` is the pair
L-polynomial of `(Q, Q')` for every nontrivial `ψ` and self-dual `ν`, and
`1 / P(q^(-s))` is the arithmetic L-factor of the uncentered special blocks
`σ ⊗ Sp(a + 1)` and `τ ⊗ Sp(b + 1)`. -/
def SegmentPairLCompatibility (c0 : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
    ∀ {d a t b : ℕ} (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
      (τ : IrreducibleWeilClass.{uF, uP} F t.succPNat)
      (B B' : Weil.Local.LocalWeilRepresentation.{uF, uP} F),
      FiniteRepresentation.classOf B = weilClassForget F σ →
      FiniteRepresentation.classOf B' = weilClassForget F τ →
      ∀ {n n' : ℕ} (Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier))
        (Q' : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n' F.Carrier)),
        IsSegmentHeadModel F (segmentOf F c0 σ a) Q →
        IsSegmentHeadModel F (segmentOf F c0 τ b) Q' →
        ∃ P : ℂ[X],
          RankinSelberg.IsPadicRankLPolynomial F ψ ν Q.representation Q'.representation P ∧
          arithmeticPairLFactor F
              (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
                (Weil.Local.localNormCharacter F).toMonoidHom B (a + 1)))
              (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
                (Weil.Local.localNormCharacter F).toMonoidHom B' (b + 1))) =
            (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹

/-- Full pair L compatibility of an assembly from the four premises and the
existence of self-dual measures. The JPSS polynomial of `(c D, c D')` is the
product of the block-pair polynomials of one pair of presenting data, and each of
these is the inverse of the arithmetic L-factor of the corresponding block pair. -/
theorem fullPairLCompatibility_of_segmentPairs
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hS : SegmentPairLCompatibility F c0)
    (hν : ∀ ψ : NontrivialAdditiveCharacter F,
      ∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν)
    (hc : IsAssemblyOf F c0 c) :
    FullPairLCompatibility F c := by
  intro ψ r t D D'
  refine ⟨hν ψ, fun ν hνψ => ?_⟩
  obtain ⟨k, dd, m, σ, ⟨B, AD, hB, hAD, ⟨hsum⟩⟩, A, J, hA, hJh, ⟨hJA⟩⟩ := hc r.succPNat D
  obtain ⟨k', dd', m', τ, ⟨B', AD', hB', hAD', ⟨hsum'⟩⟩, A', J', hA', hJh', ⟨hJA'⟩⟩ :=
    hc t.succPNat D'
  obtain ⟨d0, hd0, φ0, hφ0⟩ := hP k (fun i => segmentOf F c0 (σ i) (m i)) J hJh
  obtain ⟨d0', hd0', φ0', hφ0'⟩ := hP k' (fun j => segmentOf F c0 (τ j) (m' j)) J' hJh'
  obtain ⟨P, Q, hPJ, hQ, hPQ⟩ := hJ p F ψ ⟨ν, hνψ⟩ r t d0 d0' J J' hd0 hd0'
  refine ⟨P, ⟨A, A', J, J', hA, hA', ⟨hJA⟩, ⟨hJA'⟩, hPJ⟩, ?_⟩
  have hseg : ∀ l l', arithmeticPairLFactor F
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
        (Weil.Local.localNormCharacter F).toMonoidHom (B (φ0 l)) (m (φ0 l) + 1)))
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
        (Weil.Local.localNormCharacter F).toMonoidHom (B' (φ0' l')) (m' (φ0' l') + 1))) =
      (algebraMap ℂ[X] (RatFunc ℂ) (Q l l'))⁻¹ := by
    intro l l'
    obtain ⟨P', hP', hL⟩ := hS ψ ν hνψ (σ (φ0 l)) (τ (φ0' l')) (B _) (B' _) (hB _) (hB' _)
      _ _ (hφ0 l) (hφ0' l')
    rw [hL, RankinSelberg.IsPadicRankLPolynomial.unique hP' (hQ l l')]
  have hprod : (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ =
      ∏ l, ∏ l', (algebraMap ℂ[X] (RatFunc ℂ) (Q l l'))⁻¹ := by
    rw [hPQ, map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [map_prod, ← Finset.prod_inv_distrib]
  rw [← hAD, ← hAD', hD _ _ AD AD' ⟨hsum⟩ ⟨hsum'⟩, hprod, ← Equiv.prod_comp φ0]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Equiv.prod_comp φ0']
  exact Finset.prod_congr rfl fun l' _ => hseg l l'

/-- Segment-level L inheritance: every supercuspidal correspondence satisfies
segment-pair L compatibility. -/
def SupercuspidalSegmentPairLInheritance : Prop :=
  ∀ c0 : SupercuspidalMap.{uF, uP, uA} F,
    IsSupercuspidalCorrespondence F c0 → SegmentPairLCompatibility F c0

/-- Pair L-factor inheritance of the assembly from multisegment datum existence,
JPSS (9.5) in product form, arithmetic multiplicativity and segment-level
inheritance. -/
theorem assemblyLInheritance_of_segmentPairs
    (hP : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hS : SupercuspidalSegmentPairLInheritance.{uF, uP, uA} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F := by
  intro c0 c hc0 hc
  exact fullPairLCompatibility_of_segmentPairs F hP hJ hD (hS c0 hc0)
    (hc0.exists_selfDualMeasure F) hc

end Langlands.Correspondence
