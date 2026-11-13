import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.HarmonicAnalysis.Conductor
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.Predicates
import Langlands.WeilDeligne.Twist

/-! # Stable pair gamma comparison under highly ramified twists

For generic irreducible classes `π`, `π'` of `GL_(r+1)(K)`, `GL_(t+1)(K)` and continuous
Weil–Deligne classes `X`, `Y` of ranks `r + 1`, `t + 1` whose determinants are the central
characters of `π`, `π'` pulled back by the base reciprocity map, the pair gamma factors of
`π ⊗ χ × π'` and `(X ⊗ χ) ⊗ Y` agree for every sufficiently ramified quasi-character `χ`
(Henniart 1986, Lemma 4.2 and §4.3). Proposition definition only.
-/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

/-- Stable comparison of pair gamma factors under highly ramified twists of the first
factor. Hypotheses: a common-closure local-constant system `ε` for `eC`, a candidate `e`
agreeing with `eC` on the base field, an arbitrary nontrivial additive character `ψ`;
classes `π`, `π'` with generic representatives; quasi-characters `ω`, `ω'` by which the
scalar matrices act on `π`, `π'`; and pair classes `X`, `Y` with continuous representatives
of ranks `r + 1`, `t + 1` whose determinant characters are `ω ∘ e`, `ω' ∘ e`. Conclusion:
some bound `A` such that for every quasi-character `χ` of conductor at least `A` and every
class `πχ` that is the twist of `π` by `χ ∘ det`, `γ(s, πχ × π', ψ) = γ(s, (X ⊗ χ ∘ e) ⊗ Y, ψ)`
in the sense of `IsPairGammaMatch`. -/
def StableTwistPairGammaMatchStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (e : Correspondence.ReciprocityCandidate K),
    Correspondence.IsBaseReciprocity K e eC →
    ∀ (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
      (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
      (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
      (ω ω' : Correspondence.QuasiCharacter K)
      (X Y : Correspondence.LocalPairClass.{u, uV} K),
      (∃ A : Correspondence.AutomorphicObject.{u, u} K r.succPNat,
        Correspondence.automorphicClassOf K A = π ∧
          (letI := K.canonicalTopologicalData.topology
           letI := K.canonicalGeneralLinearTopology (r + 1)
           Whittaker.IsGeneric ψ r A.obj.representation)) →
      (∃ A' : Correspondence.AutomorphicObject.{u, u} K t.succPNat,
        Correspondence.automorphicClassOf K A' = π' ∧
          (letI := K.canonicalTopologicalData.topology
           letI := K.canonicalGeneralLinearTopology (t + 1)
           Whittaker.IsGeneric ψ t A'.obj.representation)) →
      (∀ a : K.Carrierˣ, Correspondence.CentralActsBy K π a (ω a)) →
      (∀ a : K.Carrierˣ, Correspondence.CentralActsBy K π' a (ω' a)) →
      (∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B = X ∧ B.rank = r + 1 ∧
          B.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω) →
      (∃ B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B' = Y ∧ B'.rank = t + 1 ∧
          B'.toFiniteRepresentation.IsContinuous ∧
          FiniteRepresentation.determinantCharacter B'.toFiniteRepresentation =
            Correspondence.weilCharacter K e ω') →
      ∃ A : ℕ, ∀ χ : Correspondence.QuasiCharacter K,
        A ≤ K.canonicalTopologicalData.multiplicativeConductor χ →
        ∀ πχ : Correspondence.AutomorphicClass.{u, u} K r.succPNat,
          Correspondence.IsCharacterTwist K χ π πχ →
          IsPairGammaMatch K eC ε hε ψ πχ π'
            (WeilDeligneRepresentation.twistClass (Correspondence.weilCharacter K e χ) X) Y

end Langlands.ClassField.Global.RelativeWeilGroup
