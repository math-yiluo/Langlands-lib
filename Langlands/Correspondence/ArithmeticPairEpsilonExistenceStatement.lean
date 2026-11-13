import Langlands.Correspondence.ArithmeticFactors
import Langlands.Weil.Local.Parameters
import Langlands.Weil.Representation.Predicates

/-! # Existence of arithmetic pair epsilon factors

For a `p`-adic field `K`, a common-closure local-constant system `ε` and a nontrivial
additive character `ψ`, every pair `(X, Y)` of Weil–Deligne classes with continuous
representatives has an arithmetic pair epsilon factor of the monomial form `c q^(-ms)`
(Tate 1979, (3.4.5) and (4.1.6); Deligne 1973, (5.5.2) and §8). Proposition definition only.
-/

noncomputable section

namespace Langlands.Correspondence

universe u uV uE

/-- Existence of the arithmetic pair epsilon factor. Hypotheses: a common-closure
local-constant system `ε` for `eC`, an arbitrary nontrivial additive character `ψ`, and
pair classes `X`, `Y` with representatives whose underlying Weil representations are
continuous (monodromy arbitrary). Conclusion: some `c : ℂˣ` and `m : ℤ` with
`IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m`, that is, admissible bottom-field data
and a geometric Frobenius exist, and at every admissible choice the epsilon factor of
`X ⊗ Y` is `c q^(-ms)`. -/
def ArithmeticPairEpsilonExistenceStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (X Y : LocalPairClass.{u, uV} K),
    (∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
      WeilDeligneRepresentation.classOf B = X ∧ B.toFiniteRepresentation.IsContinuous) →
    (∃ B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
      WeilDeligneRepresentation.classOf B' = Y ∧ B'.toFiniteRepresentation.IsContinuous) →
    ∃ (c : ℂˣ) (m : ℤ), IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m

end Langlands.Correspondence
