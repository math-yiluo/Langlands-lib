import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Tensor.Finite

/-!
# Cuspidal Jacquet modules of a product of two segment socles on one line

Zelevinsky 1980, 1.6 (with Bernstein–Zelevinsky 1977, 2.12) and 3.1. Let `ρ` be
an irreducible supercuspidal class of rank `r`, and let `Δ₀ = [ν^a₀ ρ, ν^(a₀+m₀-1) ρ]`
and `Δ₁ = [ν^a₁ ρ, ν^(a₁+m₁-1) ρ]` be segments on the line of `ρ`. The normalized
Jacquet module of `⟨Δ₀⟩ × ⟨Δ₁⟩` along the uniform shape `(r, …, r)` has one
composition factor for each shuffle of the two increasing runs of exponents.

This is a proposition definition, not a proof.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The exponent at position `i` of the shuffle `S ⊆ {0, …, m-1}` of the two
increasing runs `a₀, a₀ + 1, …` and `a₁, a₁ + 1, …`: the positions in `S` carry the
first run and the others carry the second, each in increasing order. So `i ∈ S`
gets `a₀ + #{j ∈ S | j < i}` and `i ∉ S` gets `a₁ + #{j ∉ S | j < i}`. -/
def shuffleExponent {m : ℕ} (S : Finset (Fin m)) (a₀ a₁ : ℝ) (i : Fin m) : ℝ :=
  if i ∈ S then a₀ + ((S.filter (· < i)).card : ℝ)
  else a₁ + ((Sᶜ.filter (· < i)).card : ℝ)

/-- The block factors `ν^(e_S(i)) A` of the uniform shape `(r, …, r)` for the
shuffle `S`, where `e_S` is `shuffleExponent S a₀ a₁`. -/
def shuffleFactors {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (m : ℕ) (hr : 0 < r) (S : Finset (Fin m)) (a₀ a₁ : ℝ) :
    letI := T.topology
    ∀ i : Fin (BlockShape.uniform m r hr).length,
      SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier) :=
  fun i => T.segmentFactor A (shuffleExponent (m := m) S a₀ a₁ i)

/-- Zelevinsky 1980, 1.6 and 3.1, for two segment socles on one cuspidal line.
Let `A` be an actual supercuspidal representative of `ρ`, of rank `r`, and let
`d` be a datum on `GL_((m₀+m₁) r)` with two segments, `Δ₀ = d.segments 0` with
beginning `ν^a₀ ρ` and length `m₀`, and `Δ₁ = d.segments 1` with beginning
`ν^a₁ ρ` and length `m₁`, whose blocks are socles `⟨Δ₀⟩`, `⟨Δ₁⟩`. Let `C` be the
uniform shape `(r, …, r)` with `m₀ + m₁` blocks and `J` the normalized Jacquet
module of `⟨Δ₀⟩ × ⟨Δ₁⟩ = d.induced` along `C`. Then `J` has composition length
`(m₀+m₁).choose m₀`, and for every irreducible representation `τ` of the Levi
its Jordan–Hölder multiplicity in `J` is the number of shuffles `S` with
`#S = m₀` whose tensor `⊗ᵢ ν^(e_S(i)) A` is equivalent to `τ`. -/
def TwoSegmentSocleShuffleJacquet : Prop :=
  letI := T.topology
  ∀ (ρ : CuspidalDatum.{uV, uF} T)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (a₀ a₁ : ℝ) (m₀ m₁ : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((m₀ + m₁) * ρ.rank)) (h₂ : d.length = 2),
    ρ.IsRepresentedBy A → d.HasSegmentSocles →
    (d.segments ⟨0, by omega⟩).base = ρ.twist a₀ →
    (d.segments ⟨0, by omega⟩).length = m₀ →
    (d.segments ⟨1, by omega⟩).base = ρ.twist a₁ →
    (d.segments ⟨1, by omega⟩).length = m₁ →
      let C := BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos
      let J := CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj
      HasCompositionSeriesLength J ((m₀ + m₁).choose m₀) ∧
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (τ : Representation ℂ (C.Levi F.Carrier) W),
          Representation.IsIrreducible τ →
            ∀ m : ℕ, HasJordanHolderMultiplicity J (Rep.of τ) m ↔
              m = Nat.card {S : Finset (Fin (m₀ + m₁)) // S.card = m₀ ∧
                Nonempty ((FiniteTensor.externalSmoothObject
                  (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)).representation.Equiv
                    τ)}

end Langlands.Classification
