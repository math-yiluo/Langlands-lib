import Langlands.Representation.Classification.TadicExhaustionLemmasStatement
import Langlands.Representation.Classification.BernsteinUnitaryStatement
import Langlands.Representation.Classification.TadicComplementarySeriesStatement
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.Representation.Aubert.GradedInductionRingLawsProof

/-!
# Inputs of Tadić's proof of Lemma 4.8(ii) and the reduction to them

Three further results used in Tadić's proof of Lemma 4.8(ii) (1986, pp.360-361), stated
for actual smooth complex representations of `GL_n(F)`:

* Zelevinsky 1980, Proposition 8.5: a normalized product of Zelevinsky socles whose
  multisegments are mutually unlinked is the Zelevinsky socle of the sum;
* Tadić 1986, Proposition 3.8: the classes `⟨a(n,d)^ρ⟩` are prime elements of the
  Grothendieck ring `R`;
* Tadić 1986, §2.1-2.4: the multisegment of an irreducible unitarizable representation is
  invariant under the Hermitian involution `a ↦ a^+`.

Together with Bernstein's Theorem 2.5(i) and (iii) and Tadić's Proposition 2.9 (published
in `BernsteinUnitaryStatement` and `TadicComplementarySeriesStatement`) they form
`TadicBlockReductionInputs`, and `TadicBlockReductionFromInputs` asserts that these inputs
imply `TadicBlockReduction`. All assertions are proposition definitions; none is proved.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Zelevinsky 1980, Proposition 8.5, printed p.196: let `a_1, …, a_p` be multisegments
such that for `i ≠ j` no segment of `a_i` is linked with a segment of `a_j`. Then
`⟨a_1⟩ × ⋯ × ⟨a_p⟩ = ⟨a_1 + ⋯ + a_p⟩`. Stated for a block shape `B` and Zelevinsky
socles `π i` of `a i`: the normalized product of the `π i` is a Zelevinsky socle of
`∑ i, a i` (in particular it is irreducible). -/
def UnlinkedSocleProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n) (a : Fin B.length → T.Multisegment.{max uF uV, uF})
    (π : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (a i).IsZelevinskySocle (π i)) →
    (∀ i j, i ≠ j → ∀ Δ ∈ a i, ∀ Δ' ∈ a j, ¬ Δ.IsLinked Δ') →
      (∑ i, a i).IsZelevinskySocle ((T.normalizedProductInductionFunctor B).obj π)

/-- Tadić 1986, Proposition 3.8, printed p.354: for `n, d > 0` and every cuspidal `ρ`
(unitary or not), `⟨a(n,d)^ρ⟩` is a prime element of the Grothendieck ring `R`. Here
`R` is the published graded ring `Aubert.gradedInductionRing` of actual finite-length
representations with the normalized induction product, built from the published proofs
of its exactness and ring laws, and the class of a Zelevinsky socle `π` of `a(n,d)^ρ` on
`GL_N` is its class in degree `N` (for any finite-length witness). -/
def TadicRectangleSoclePrime : Prop :=
  letI := T.topology
  letI := Aubert.gradedInductionRing.{uF, uV} F T (Aubert.binaryProductExactness F T)
    (Aubert.gradedInductionRingLaws F T (Aubert.binaryProductExactness F T))
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d), 0 < n →
    ∀ {N : ℕ} (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      (tadicMultisegment ρ n d hd).IsZelevinskySocle π →
        ∀ hπ : π.HasFiniteLength,
          Prime (Aubert.gradedInclusion F T N (finiteLengthClass N F.Carrier π hπ))

open scoped Classical in
/-- Tadić 1986, §2.1-2.4, printed pp.345-346: an irreducible unitarizable `π = ⟨a⟩` is
Hermitian, `π ≅ π^+`, and `⟨a⟩^+ = ⟨a^+⟩`; with Zelevinsky's classification this gives
`a^+ = a`. For a unitary cuspidal `ρ` one has `(ν^x ρ)^+ = ν^(-x) ρ`, so the Hermitian dual
of the segment `[ν^x ρ, ν^(x+l-1) ρ]` is `[ν^(-(x+l-1)) ρ, ν^(-x) ρ]`. Since every cuspidal
datum is a real twist of a unitary one (§2.3), `a^+ = a` says exactly that these two
segments occur in `a` with the same multiplicity, for every unitary `ρ`, real `x` and
length `l > 0`. -/
def UnitarizableSocleHermitianSymmetry : Prop :=
  letI := T.topology
  ∀ {N : ℕ} (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (a : T.Multisegment.{max uF uV, uF}),
    Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
      a.IsZelevinskySocle π →
        ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}), ρ.IsUnitary →
          ∀ (x : ℝ) (l : ℕ) (hl : 0 < l),
            a.count (⟨ρ.twist x, l, hl⟩ : T.Segment.{max uF uV, uF}) =
              a.count (⟨ρ.twist (-(x + ((l : ℝ) - 1))), l, hl⟩ : T.Segment.{max uF uV, uF})

/-- The inputs of Tadić's proof of Lemma 4.8(ii): Bernstein's Theorem 2.5(i) and (iii),
Tadić's Proposition 2.9, Zelevinsky's Proposition 8.5, Tadić's Proposition 3.8 and the
Hermitian symmetry of unitarizable representations. -/
def TadicBlockReductionInputs : Prop :=
  BernsteinUnitaryProductIrreducibility.{uF, uV} F T ∧
    BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T ∧
    ComplementarySeriesUnitarity.{uF, uV} F T ∧
    UnlinkedSocleProductIrreducibility.{uF, uV} F T ∧
    TadicRectangleSoclePrime.{uF, uV} F T ∧
    UnitarizableSocleHermitianSymmetry.{uF, uV} F T

/-- Tadić's proof of Lemma 4.8(ii) as an implication: the inputs imply
`TadicBlockReduction`. -/
def TadicBlockReductionFromInputs : Prop :=
  TadicBlockReductionInputs.{uF, uV} F T → TadicBlockReduction.{uF, uV} F T

end Langlands.Classification
