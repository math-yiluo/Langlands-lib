import Langlands.Representation.Classification.SpehIsomorphismAdapters
import Langlands.Representation.Classification.TadicMultisegments

/-! Bounded conversion from rectangular-socle X-blocks to actual Speh blocks. -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

variable (F T) in
/-- The bounded Speh-realization consequence needed from rectangular-socle
comparison. This is an explicit hypothesis, not an assertion of that comparison. -/
def TadicSocleSpehComparison (k : ℕ) : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV,uF}) (n d : ℕ) (hd : 0 < d),
    0 < n → ρ.IsUnitary →
    ∀ {N : ℕ} (σ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear N F.Carrier)),
      N ≤ k → (tadicMultisegment ρ n d hd).IsZelevinskySocle σ →
      ∃ (D : SpehDatum.{uF,uV} F T)
        (S : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear D.degree F.Carrier))
        (h : D.degree = N), D.IsSpeh S ∧ Nonempty ((h ▸ S) ≅ σ)

/-- Restrict a supplied comparison to a smaller underlying-socle rank bound. -/
theorem TadicSocleSpehComparison.mono {j k : ℕ} (hjk : j ≤ k)
    (h : TadicSocleSpehComparison.{uF,uV} F T k) : TadicSocleSpehComparison.{uF,uV} F T j := by
  let := T.topology
  intro ρ n d hd hn hρ N σ hNj hσ
  exact h ρ n d hd hn hρ σ (hNj.trans hjk) hσ

/-- A comparison only through socle rank `k` converts all of `X_k`, including
its complementary products whose final rank may exceed `k`. -/
theorem isTadicBuildingBlock_of_isTadicXBlock {k N : ℕ}
    (hcomp : TadicSocleSpehComparison.{uF,uV} F T k) :
    letI := T.topology
    ∀ {τ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear N F.Carrier)},
      IsTadicXBlock k τ → IsTadicBuildingBlock F T τ := by
  let := T.topology
  intro τ hτ
  rcases hτ with ⟨ρ,n,d,hd,hn,hρ,hNk,hσ⟩ |
    ⟨ρ,n,d,hd,M,hM,σ,α,hMN,hn,hρ,hMk,hσ,hα0,hα,⟨eτ⟩⟩
  · obtain ⟨D,S,hD,hS,eS⟩ := hcomp ρ n d hd hn hρ τ hNk hσ
    exact Or.inl ⟨D,S,hD,hS,eS⟩
  · obtain ⟨D,S,hD,hS,⟨eS⟩⟩ := hcomp ρ n d hd hn hρ σ hMk hσ
    cases hMN
    exact Or.inr ⟨D,S,α,congrArg (fun r => 2 * r) hD,hS,hα0,hα,
      ⟨D.complementaryRankIso hM hD S σ eS α ≪≫ eτ⟩⟩

end Langlands.Classification
