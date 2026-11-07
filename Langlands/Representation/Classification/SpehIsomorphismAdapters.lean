import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! Actual isomorphism adapters for Speh and complementary building blocks. -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SpehDatum

/-- The actual quotient relation and uniqueness survive an isomorphism of
the candidate Speh representation. -/
theorem IsSpeh.of_iso (d : SpehDatum.{uF,uV} F T) :
    letI := T.topology
    ∀ {S S' : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier)},
      d.IsSpeh S → (S ≅ S') → d.IsSpeh S' := by
  let := T.topology
  intro S S' hs e
  let E := SmoothRep.equivOfIso e
  obtain ⟨hS, q, hq⟩ := hs.2.1
  refine ⟨hs.1, ⟨(Weil.IsomorphismInvariance.irreducible_iff E).mp hS,
    E.toIntertwiningMap.comp q, E.surjective.comp hq⟩, ?_⟩
  intro π hπ
  obtain ⟨eπ⟩ := hs.2.2 π hπ
  exact ⟨eπ ≪≫ e⟩

/-- Isomorphic supplied representations give isomorphic same-representation
complementary products, preserving the two opposite exponents. -/
def complementaryInducedIso (d : SpehDatum.{uF,uV} F T) :
    letI := T.topology
    ∀ {S S' : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier)},
      (S ≅ S') → ∀ α : ℝ,
        d.complementaryInduced S α ≅ d.complementaryInduced S' α := by
  let := T.topology
  intro S S' e α
  exact T.twistedProductInducedIso
    (BlockShape.uniform 2 d.degree (Nat.mul_pos d.length_pos d.rank_pos))
    (fun _ => e) (fun i => if (i : ℕ) = 0 then α else -α)

/-- Move the original Speh rank equality through the entire complementary
induction, then change both copies by the same supplied isomorphism. -/
def complementaryRankIso (d : SpehDatum.{uF,uV} F T)
    {m : ℕ} (hm : 0 < m) (h : d.degree = m) :
    letI := T.topology
    ∀ (S : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
      (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)),
      ((h ▸ S) ≅ A) → ∀ α : ℝ,
        (congrArg (fun r => 2 * r) h ▸ d.complementaryInduced S α) ≅
          T.twistedProductInduced (BlockShape.uniform 2 m hm)
            (fun _ => A) (fun i => if (i : ℕ) = 0 then α else -α) := by
  cases h
  let := T.topology
  intro S A e α
  exact d.complementaryInducedIso e α

end SpehDatum

/-- A supplied Speh witness identifies the whole complementary product as
an actual building block, with the exact doubled-rank equality. -/
theorem isTadicBuildingBlock_complementary_of_spehIso
    (d : SpehDatum.{uF,uV} F T) {m : ℕ} (hm : 0 < m) (h : d.degree = m) :
    letI := T.topology
    ∀ (S : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
      (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)),
      d.IsSpeh S → ((h ▸ S) ≅ A) →
        ∀ α : ℝ, 0 < α → α < (1 / 2 : ℝ) →
          IsTadicBuildingBlock F T
            (T.twistedProductInduced (BlockShape.uniform 2 m hm)
              (fun _ => A) (fun i => if (i : ℕ) = 0 then α else -α)) := by
  let := T.topology
  intro S A hs e α hα0 hα
  exact Or.inr ⟨d, S, α, congrArg (fun r => 2 * r) h, hs, hα0, hα,
    ⟨d.complementaryRankIso hm h S A e α⟩⟩

end Langlands.Classification
