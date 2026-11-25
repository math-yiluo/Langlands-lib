# Tadic's generic-free unitary-dual exhaustion

Module
`Langlands.Representation.Classification.TadicUnitaryDualExhaustionProof`.

## Statement proved

```lean
theorem Langlands.Classification.tadicUnitaryDualExhaustion :
    TadicUnitaryDualExhaustion.{uF, uV} F T
```

The theorem holds for every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every `T : F.TopologicalData`, and independent field and
representation universes `uF` and `uV`. Its type is exactly the published
proposition `Langlands.Classification.TadicUnitaryDualExhaustion.{uF, uV} F T` of
`Langlands/Representation/Classification/TadicUnitaryStatement.lean`. The theorem
has no hypotheses. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The proposition is the exhaustion clause of Tadic 1986, Theorem D(ii) (printed
pp.338–339; see also section 7.4, Theorem 7.5(ii), and Appendix A.10). Take any
`n : ℕ` and any actual smooth complex representation
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)`. If `π` is
irreducible and unitarizable, then there are a block shape `B : BlockShape (n + 1)`
and representations `σ i` of `GL_(B.size i)` with the following two properties:

- each `σ i` satisfies `IsTadicBuildingBlock F T`;
- `π` is isomorphic to the whole normalized upper-block induction
  `(T.normalizedProductInductionFunctor B).obj σ`.

A building block is one of two kinds. The first is a representation isomorphic, via
the rank transport `d.degree = n`, to a Speh representation `S` with `d.IsSpeh S`.
The second is isomorphic, via the rank transport `2 * d.degree = n`, to the
complementary product `d.complementaryInduced S α` of one Speh representation `S`
with itself, where `0 < α < 1/2`. The theorem leaves the statement unchanged. In
particular it adds no genericity, Hermitian-matching or classification premise.

## Proof

The proof is a single term. It applies the published theorem
`tadicExhaustionReduction F T` (module
`Classification.TadicExhaustionReductionProof`) to published proofs of all its
hypotheses. That theorem proves `TadicExhaustionReduction.{uF, uV} F T`, the
implication

`TadicExhaustionLemmaStatements → SpehUnitarizability →
MultisegmentHeadClassification → TadicUnitaryDualExhaustion`.

This implication is Tadic's proof of Theorem A.10 (printed pp.378–379). It runs by
induction on the rank. In every rank it proves `⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` for
unitary `ρ`. It then uses Lemma 4.8(ii) to factor every irreducible unitarizable
representation into building blocks. The details are in
`TadicExhaustionReductionProof.md` and the assembly modules that file names.

The hypotheses are supplied as follows. Each is taken at the same `p`, `F`, `T`,
`uF` and `uV`.

1. `TadicExhaustionLemmaStatements.{uF, uV} F T` is a conjunction of three
   propositions. The anonymous constructor `⟨_, _, _⟩` supplies them:
   - `tadicBlockReduction F T` (module `Classification.TadicBlockReductionProof`)
     proves `TadicBlockReduction`, Tadic 1986, Lemma 4.8(ii), existence part.
     Assume `(U^m)`. Then every irreducible unitarizable representation of
     `GL_(m+1)` that is not a Zelevinsky socle `⟨a(n,d)^ρ⟩` with `n > 0` and `ρ`
     unitary is a normalized product of members of `X_m`.
   - `TadicRectangleHeadSocle.tadicRectangleHeadSocleDistinct F T` (module
     `Classification.TadicRectangleHeadSocleDistinctProof`) proves
     `TadicRectangleHeadSocleDistinct`, Tadic 1986, Lemma 6.3: for `0 < n < d`,
     `L(a(n,d)^ρ) ≇ ⟨a(n,d)^ρ⟩`.
   - `irreducibleLanglandsHeadProduct F T` (module
     `Classification.IrreducibleLanglandsHeadProductProof`) proves
     `IrreducibleLanglandsHeadProduct`, Tadic 1986, Corollary A.6(ii) for finitely
     many factors. If a normalized product of Langlands heads `L(a_i)` is
     irreducible, it is the Langlands head `L(∑ a_i)`.
2. `spehUnitarizability F T` (module `Classification.SpehUnitarizabilityProof`)
   proves `SpehUnitarizability`, Tadic 1986, Theorem A.8: every representation
   satisfying the Speh relation for a discrete-series datum is unitarizable.
3. `multisegmentHeadClassification F T` (module
   `Classification.MultisegmentHeadClassificationProof`) proves
   `MultisegmentHeadClassification`, the Langlands classification in multiset form
   (Rodier 1982, §4.3, Theorem 3(b)). Two Langlands heads are isomorphic exactly
   when their multisegments are equal.

Each of these theorems is an unconditional theorem in the Library. The composition
is therefore unconditional as well.

## Provenance

The composition follows Tadic's own
structure for the exhaustion half of Theorem D(ii): the induction of Theorem A.10,
using Lemma 4.8(ii), Lemma 6.3, Corollary A.6(ii), Theorem A.8 and the
classification of Langlands quotients. Some of the published ingredient proofs
take routes other than Tadic's; their own Markdown files describe those routes.
