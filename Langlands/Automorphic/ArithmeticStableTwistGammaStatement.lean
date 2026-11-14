import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.HarmonicAnalysis.Conductor
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.Predicates
import Langlands.WeilDeligne.Twist

/-! # Arithmetic pair gamma factors after highly ramified twists

For continuous Weil–Deligne classes `X`, `X₀` of rank `r + 1` with the same determinant
character, and `Y`, `Y₀` of rank `t + 1` with the same determinant character, the arithmetic
pair gamma factors of `(X ⊗ χ) ⊗ Y` and `(X₀ ⊗ χ) ⊗ Y₀` agree for every sufficiently ramified
quasi-character `χ` (Henniart 1986, Lemma 4.2 (1)–(2), from Deligne–Henniart 1981,
Théorème 4.6). Proposition definition only.
-/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

/-- Arithmetic stability of pair gamma factors under highly ramified twists of the first
factor. Hypotheses: a common-closure local-constant system `ε` for `eC`, a candidate `e`
agreeing with `eC` on the base field, an arbitrary nontrivial additive character `ψ`,
quasi-characters `ω`, `ω'`, and pair classes `X`, `X₀` (resp. `Y`, `Y₀`) with continuous
representatives of rank `r + 1` (resp. `t + 1`) whose determinant characters are `ω ∘ e`
(resp. `ω' ∘ e`). Conclusion: some bound `A` such that for every quasi-character `χ` of
conductor at least `A`, every arithmetic gamma factor of `(X₀ ⊗ χ ∘ e) ⊗ Y₀` is one of
`(X ⊗ χ ∘ e) ⊗ Y`. -/
def ArithmeticStableTwistGammaStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (e : Correspondence.ReciprocityCandidate K),
    Correspondence.IsBaseReciprocity K e eC →
    ∀ (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
      (ω ω' : Correspondence.QuasiCharacter K)
      (X X₀ Y Y₀ : Correspondence.LocalPairClass.{u, uV} K),
      (∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B = X ∧ B.rank = r + 1 ∧
          B.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω) →
      (∃ B₀ : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B₀ = X₀ ∧ B₀.rank = r + 1 ∧
          B₀.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B₀.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω) →
      (∃ B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B' = Y ∧ B'.rank = t + 1 ∧
          B'.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B'.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω') →
      (∃ B₀' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B₀' = Y₀ ∧ B₀'.rank = t + 1 ∧
          B₀'.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B₀'.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω') →
      ∃ A : ℕ, ∀ χ : Correspondence.QuasiCharacter K,
        A ≤ K.canonicalTopologicalData.multiplicativeConductor χ →
        ∀ G : RatFunc ℂ,
          Correspondence.IsArithmeticPairGammaFactor K eC ε hε ψ
              (WeilDeligneRepresentation.twistClass (Correspondence.weilCharacter K e χ) X₀)
              Y₀ G →
            Correspondence.IsArithmeticPairGammaFactor K eC ε hε ψ
              (WeilDeligneRepresentation.twistClass (Correspondence.weilCharacter K e χ) X)
              Y G

end Langlands.ClassField.Global.RelativeWeilGroup
