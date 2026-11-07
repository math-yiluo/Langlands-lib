import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Category.Subquotients

/-!
# Complementary series of `GL_n`: unitarity and length bounds

Tadic 1986, Propositions 2.9 and 2.10, for the actual normalized upper-block
product `π(σ, α) = ν^α σ × ν^(-α) σ` of an irreducible unitarizable smooth
representation `σ` of `GL_n(F)`. Composition factors are irreducible actual
subquotients. All assertions below are proposition definitions; none is proved.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual complementary product `π(σ, α) = ν^α σ × ν^(-α) σ` on `GL_(2n)`:
normalized upper-block induction of the uniform two-block shape, with the very
same representation `σ` in both blocks and exponents `α, -α` in that order. -/
def complementaryProduct {n : ℕ} (hn : 0 < n)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (α : ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * n) F.Carrier) :=
  T.twistedProductInduced (BlockShape.uniform 2 n hn) (fun _ => σ)
    (fun i => if (i : ℕ) = 0 then α else -α)

/-- The Speh complementary induction is this construction at the Speh rank. -/
theorem SpehDatum.complementaryInduced_eq_complementaryProduct
    (d : SpehDatum.{uF, uV} F T)
    (S : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (α : ℝ) :
    d.complementaryInduced S α =
      complementaryProduct F T (Nat.mul_pos d.length_pos d.rank_pos) S α :=
  rfl

/-- Tadic 1986 Proposition 2.9, p.350: for irreducible unitarizable `σ` of
`GL_n`, `0 < n`, and `α₀ > 0`, if `π(σ, α)` is irreducible for every
`α ∈ (-α₀, α₀)`, then `π(σ, α)` is unitarizable for every such `α`, and every
irreducible subquotient of `π(σ, α₀)` is unitarizable. -/
def ComplementarySeriesUnitarity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (hn : 0 < n)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (α₀ : ℝ),
    Representation.IsIrreducible σ.representation → IsUnitarizable σ.representation →
      0 < α₀ →
      (∀ α ∈ Set.Ioo (-α₀) α₀,
        Representation.IsIrreducible (complementaryProduct F T hn σ α).representation) →
      (∀ α ∈ Set.Ioo (-α₀) α₀,
        IsUnitarizable (complementaryProduct F T hn σ α).representation) ∧
      ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (2 * n) F.Carrier),
        Representation.IsIrreducible τ.representation →
          SmoothRep.IsSubquotient τ (complementaryProduct F T hn σ α₀) →
            IsUnitarizable τ.representation

/-- Tadic 1986 Proposition 2.10(i), p.350: for irreducible unitarizable `σ` of
`GL_n`, `0 < n`, some `α₀ > 0` makes `π(σ, α)` irreducible for every
`α ∈ (-α₀, α₀)`. -/
def ComplementarySeriesIrreducibilityNearZero : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (hn : 0 < n)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    Representation.IsIrreducible σ.representation → IsUnitarizable σ.representation →
      ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioo (-α₀) α₀,
        Representation.IsIrreducible (complementaryProduct F T hn σ α).representation

/-- Tadic 1986 Proposition 2.10(ii), pp.350–351, for unitarizable `σ`: if
`π(σ, α)` is irreducible and unitarizable for every `α ∈ (β, γ)`, `β < γ`, then
`γ - β ≤ 1`, and if `γ - β = 1` then neither `π(σ, β)` nor `π(σ, γ)` is
irreducible. -/
def ComplementarySeriesLengthBound : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (hn : 0 < n)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (β γ : ℝ),
    Representation.IsIrreducible σ.representation → IsUnitarizable σ.representation →
      β < γ →
      (∀ α ∈ Set.Ioo β γ,
        Representation.IsIrreducible (complementaryProduct F T hn σ α).representation ∧
          IsUnitarizable (complementaryProduct F T hn σ α).representation) →
      γ - β ≤ 1 ∧
        (γ - β = 1 →
          ¬ Representation.IsIrreducible (complementaryProduct F T hn σ β).representation ∧
            ¬ Representation.IsIrreducible (complementaryProduct F T hn σ γ).representation)

/-- Tadic 1986 Propositions 2.9, 2.10(i) and 2.10(ii) together. -/
def TadicComplementarySeriesStatements : Prop :=
  ComplementarySeriesUnitarity.{uF, uV} F T ∧
    ComplementarySeriesIrreducibilityNearZero.{uF, uV} F T ∧
    ComplementarySeriesLengthBound.{uF, uV} F T

/-- The conjunction for every prime, finite p-adic extension and compatible
topology, with independent field and representation universes. -/
def PadicTadicComplementarySeriesStatements : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    TadicComplementarySeriesStatements.{uF, uV} F T

end Langlands.Classification
