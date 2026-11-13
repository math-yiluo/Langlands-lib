import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Weil.Representation.Predicates

/-! # Pair gamma comparison for principal-series constituents

For generic irreducible subquotients `π`, `π'` of normalized principal series
`i(μ_1, …, μ_(r+1))`, `i(μ'_1, …, μ'_(t+1))` of `GL_(r+1)(K)`, `GL_(t+1)(K)`, and continuous
zero-monodromy Weil–Deligne classes `X`, `Y` whose Weil actions are upper triangular with
diagonal characters `μ_(σ i) ∘ e`, `μ'_(σ' j) ∘ e`, the pair gamma factors agree:
`γ(s, π × π', ψ) = ∏ γ(s, μ_i μ'_j, ψ) = γ(s, X ⊗ Y, ψ)`
(Henniart 1986, §2.7(iii); Jacquet–Piatetski-Shapiro–Shalika 1983, Theorem 3.1).
Proposition definition only.
-/

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

/-- Pair gamma comparison for generic principal-series constituents. Hypotheses: a
common-closure local-constant system `ε` for `eC`, a candidate `e` agreeing with `eC` on
the base field, an arbitrary nontrivial additive character `ψ`, quasi-characters
`μ : Fin (r + 1) → K^×^`, `μ' : Fin (t + 1) → K^×^`; a representative of `π` that is generic
and a subquotient of `principalSeries K r μ`, and likewise for `π'` and `μ'`; and
continuous representatives of `X`, `Y` with zero monodromy, admitting bases in which every
Weil element acts by an upper triangular matrix with diagonal entries
`μ (σ i) ∘ e`, `μ' (σ' j) ∘ e` for some permutations `σ`, `σ'`. Conclusion:
`γ(s, π × π', ψ) = γ(s, X ⊗ Y, ψ)` in the sense of `IsPairGammaMatch`. -/
def PrincipalSeriesPairGammaMatchStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (e : Correspondence.ReciprocityCandidate K),
    Correspondence.IsBaseReciprocity K e eC →
    ∀ (ψ : Correspondence.NontrivialAdditiveCharacter K) {r t : ℕ}
      (μ : Fin (r + 1) → Correspondence.QuasiCharacter K)
      (μ' : Fin (t + 1) → Correspondence.QuasiCharacter K)
      (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
      (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat)
      (X Y : Correspondence.LocalPairClass.{u, uV} K),
      (∃ A : Correspondence.AutomorphicObject.{u, u} K r.succPNat,
        Correspondence.automorphicClassOf K A = π ∧
          (letI := K.canonicalTopologicalData.topology
           letI := K.canonicalGeneralLinearTopology (r + 1)
           Whittaker.IsGeneric ψ r A.obj.representation ∧
             Correspondence.IsSubquotientOf (Correspondence.principalSeries K r μ)
               A.obj.representation)) →
      (∃ A' : Correspondence.AutomorphicObject.{u, u} K t.succPNat,
        Correspondence.automorphicClassOf K A' = π' ∧
          (letI := K.canonicalTopologicalData.topology
           letI := K.canonicalGeneralLinearTopology (t + 1)
           Whittaker.IsGeneric ψ t A'.obj.representation ∧
             Correspondence.IsSubquotientOf (Correspondence.principalSeries K t μ')
               A'.obj.representation)) →
      (∃ B : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B = X ∧ B.monodromy = 0 ∧
          B.toFiniteRepresentation.IsContinuous ∧
          ∃ (b : Module.Basis (Fin (r + 1)) ℂ B) (σ : Equiv.Perm (Fin (r + 1))),
            ∀ g : Weil.Local.localWeilGroup K,
              (∀ i j : Fin (r + 1), j < i → b.repr (B.representation g (b j)) i = 0) ∧
                ∀ i : Fin (r + 1), b.repr (B.representation g (b i)) i =
                  ((Correspondence.weilCharacter K e (μ (σ i)) g : ℂˣ) : ℂ)) →
      (∃ B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K,
        WeilDeligneRepresentation.classOf B' = Y ∧ B'.monodromy = 0 ∧
          B'.toFiniteRepresentation.IsContinuous ∧
          ∃ (b' : Module.Basis (Fin (t + 1)) ℂ B') (σ' : Equiv.Perm (Fin (t + 1))),
            ∀ g : Weil.Local.localWeilGroup K,
              (∀ i j : Fin (t + 1), j < i → b'.repr (B'.representation g (b' j)) i = 0) ∧
                ∀ i : Fin (t + 1), b'.repr (B'.representation g (b' i)) i =
                  ((Correspondence.weilCharacter K e (μ' (σ' i)) g : ℂˣ) : ℂ)) →
      IsPairGammaMatch K eC ε hε ψ π π' X Y

end Langlands.ClassField.Global.RelativeWeilGroup
