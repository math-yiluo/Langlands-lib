import Langlands.Representation.Classification.SupercuspidalDerivativesStatement
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Derivative.Iteration
import Langlands.HarmonicAnalysis.Basic

/-!
# Derivatives of cuspidal representations, segment socles and their products

Five unproved statements, together with the imported supercuspidal statement,
about the Bernstein–Zelevinsky derivatives
`Derivative.generalLinearDerivative T ψ N k hk`, for every nontrivial unitary
additive character `ψ`: Gelfand–Kazhdan for supercuspidals (BZ77 4.4),
Zelevinsky's Theorem 3.5, the support shift of highest derivatives
(Ze80 4.4(d)), Proposition 4.3 in level and lattice forms, and the highest
derivative of a product of segment socles.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- (b) Ze80 Theorem 3.5: the derivatives of a segment socle `⟨Δ⟩`. Only the
orders `0` and `Δ.rank` can be nonzero; for a singleton the order-`Δ.rank`
derivative is one-dimensional; otherwise it is the segment socle of `Δ⁻`, the
segment with the same base and one position fewer. -/
def SegmentSocleDerivatives : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : T.Segment.{uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentSocle Δ π →
      (∀ (k : ℕ) (hk : k ≤ Δ.degree), 0 < k → k ≠ Δ.rank →
        Subsingleton
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ Δ.degree k hk).obj π)) ∧
      (∀ hm : Δ.rank ≤ Δ.degree, Δ.length = 1 →
        Module.finrank ℂ
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ Δ.degree Δ.rank hm).obj
            π) = 1) ∧
      (∀ (hm : Δ.rank ≤ Δ.degree) (h₂ : 2 ≤ Δ.length)
        (hdeg : Δ.degree - Δ.rank = (Δ.length - 1) * Δ.rank),
        T.IsSegmentSocle ⟨Δ.base, Δ.length - 1, by omega⟩
          (T.castRank hdeg
            ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ Δ.degree Δ.rank hm).obj
              π)))

/-- (c) Ze80 4.4(d), from BZ77 Lemma 4.7(b): if `k` is the highest order of a
nonzero derivative of an irreducible `ω`, every irreducible subrepresentation
`σ` of `ω^(k)` satisfies `ν · supp σ ⊆ supp ω` as multisets. -/
def HighestDerivativeSupportShift : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (ω : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (k : ℕ) (hk : k ≤ n),
    ω.IsIrreducible →
    Nontrivial ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj ω) →
    (∀ (j : ℕ) (hj : j ≤ n), k < j →
      Subsingleton ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n j hj).obj ω)) →
    ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier),
      IsIrreducibleSubrepresentation
        ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
          ω).representation
        σ.representation →
      ∀ s s' : Multiset (T.CuspidalDatum.{uV, uF}),
        T.IsSupercuspidalSupport ω s → T.IsSupercuspidalSupport σ s' →
          s'.map (PadicField.TopologicalData.CuspidalDatum.twist 1) ≤ s

/-- (d) Ze80 Proposition 4.3: if no two segments of the datum are juxtaposed,
every irreducible subquotient of `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` has a nonzero derivative
of order `λ = ∑ i, (d.segments i).rank` and none of higher order. -/
def NonjuxtaposedSegmentSocleConstituentLevel : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n),
    d.HasSegmentSocles →
    (∀ i j, i ≠ j → ¬ (d.segments i).IsJuxtaposed (d.segments j)) →
    ∀ (k : ℕ) (hk : k ≤ n), k = ∑ i, (d.segments i).rank →
    ∀ ω : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      ω.IsIrreducible → SmoothRep.IsSubquotient ω d.induced →
        Nontrivial ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj ω) ∧
        ∀ (j : ℕ) (hj : j ≤ n), k < j →
          Subsingleton ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n j hj).obj ω)

/-- (e) The lattice form of Ze80 Proposition 4.3: under the hypotheses of (d),
the order-`λ` derivative strictly preserves inclusions of subrepresentations of
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩`, measured by the images of the inclusions. -/
def NonjuxtaposedSegmentSocleDerivativeStrictMono : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n),
    d.HasSegmentSocles →
    (∀ i j, i ≠ j → ¬ (d.segments i).IsJuxtaposed (d.segments j)) →
    ∀ (k : ℕ) (hk : k ≤ n), k = ∑ i, (d.segments i).rank →
    ∀ K₁ K₂ : Subrepresentation d.induced.representation, K₁ < K₂ →
      (SmoothRep.hom ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).map
          (SmoothRep.subtype d.induced K₁))).range <
        (SmoothRep.hom ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).map
          (SmoothRep.subtype d.induced K₂))).range

/-- (f) The highest derivative of a product of segment socles: no derivative of
order above `λ` is nonzero, the order-`λ` derivative is isomorphic to the
product of the `⟨Δ_i⁻⟩` (original order, singletons omitted), and it is
one-dimensional when every segment is a singleton. -/
def SegmentSocleProductHighestDerivative : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n),
    d.HasSegmentSocles →
    ∀ (k : ℕ) (hk : k ≤ n), k = ∑ i, (d.segments i).rank →
      (∀ (j : ℕ) (hj : j ≤ n), k < j →
        Subsingleton
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n j hj).obj d.induced)) ∧
      (∃ d' : T.SegmentProductDatum.{uV, uF} (n - k),
        List.ofFn d'.segments =
          (List.ofFn d.segments).filterMap (fun Δ =>
            if h : 2 ≤ Δ.length then
              some (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF})
            else none) ∧
        d'.HasSegmentSocles ∧
        Nonempty
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj d.induced ≅
            d'.induced)) ∧
      ((∀ i, (d.segments i).length = 1) →
        Module.finrank ℂ
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj d.induced) = 1)

end Langlands.Classification
