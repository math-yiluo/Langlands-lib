# Existence of epsilon factors of arbitrary irreducible pairs: proof

Author: Worker 5077. Module
`Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceProof`,
namespace `Langlands.RankinSelberg`.

`Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence` proves exactly
the published proposition
`Langlands.RankinSelberg.LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}`
of the unchanged module
[`LanglandsPairEpsilonFactorExistenceStatement`](LanglandsPairEpsilonFactorExistenceStatement.md).
The theorem has no hypotheses: its type is the statement itself, with the
three universe parameters `uF`, `uV`, `uW` kept independent.

## What is proved

For every prime `p`, every `F : PadicField.{uF} p`, every
`ψ : UnitaryAdditiveCharacter F.Carrier` (nontrivial by its type), every
supplied `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`,
all `r t : ℕ`, and all irreducible admissible
`π : SmoothRep.{0, uF, max uF uV} ℂ (GL_(r+1)(F))` and
`σ : SmoothRep.{0, uF, max uF uW} ℂ (GL_(t+1)(F))`, there is
`e : ℂˣ × ℤ` with
`IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν.val π σ e`.

The certificate is the published one, unchanged. It contains:

1. an actual `SquareIntegrableLanglandsDatum` of rank `r + 1`, with blocks in
   universe `max uF uV`, that has `π` as a Langlands quotient;
2. the same for `σ` at rank `t + 1`, with blocks in universe `max uF uW`;
3. for *every* pair of such presenting data, the statement that `e` is the
   product `epsilonFactorProduct b` of a family `b i j` of JPSS epsilon
   factors (`IsPadicRankEpsilonFactor F ψ ν.val`) of all block pairs.

The ranks are arbitrary and in either order. No unitarity or genericity of
`π`, `σ` is assumed. No Langlands datum is chosen in the statement, no factor
function is supplied, and no measure is chosen: the proof uses the given `ν`
and its self-duality property only. The universes are not lowered or
identified: the certificate stays at the saturated universes
`.{uF, max uF uV, max uF uW}` that the statement fixes.

## Implemented proof

The proof is a single term:

```
langlandsPairEpsilonFactorExistence_of_exhaustion_classification.{uF, uV, uW}
  (fun _ _ F => ⟨squareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData,
                 squareIntegrableLanglandsExhaustion.{uF, uW} F F.canonicalTopologicalData⟩)
  (fun _ _ F => ⟨squareIntegrableLanglandsClassification.{uF, uV} F F.canonicalTopologicalData,
                 squareIntegrableLanglandsClassification.{uF, uW} F F.canonicalTopologicalData⟩)
```

1. **Reduction with the block input already proved.** The published theorem
   `Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence_of_exhaustion_classification`
   (module `LanglandsPairEpsilonBlockExistence`) concludes
   `LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` from two
   hypotheses only, `hex` and `hcl`. It is itself the published reduction
   `langlandsPairEpsilonFactorExistence_of_classification` (module
   `LanglandsPairEpsilonFactorExistenceStatement`) with its third, analytic
   input `hb` discharged by the proved theorem
   `squareIntegrableDataEpsilonExistence`. That reduction applies the
   constructor `langlandsPairEpsilonFactorOfClassification` (module
   `LanglandsFactorDescent`), which takes the presenting data from exhaustion
   and derives independence of the presenting data from classification.
2. **Exhaustion (`hex`).** For each `p` and `F`, the two components are
   `Langlands.Classification.squareIntegrableLanglandsExhaustion` at
   `.{uF, uV}` and at `.{uF, uW}`, applied to `F` and
   `F.canonicalTopologicalData`. That theorem proves
   `SquareIntegrableLanglandsExhaustion.{uF, u} F T` for every
   `T : F.TopologicalData` and every carrier parameter `u`, with no
   hypothesis.
3. **Classification (`hcl`).** Likewise, the two components are
   `Langlands.Classification.squareIntegrableLanglandsClassification` at
   `.{uF, uV}` and at `.{uF, uW}`, which proves
   `SquareIntegrableLanglandsClassification.{uF, u} F T` for every `T` and
   every `u`, with no hypothesis.

The two carrier universes `uV` and `uW` are instantiated separately, so the
data of `π` have blocks in `max uF uV` and the data of `σ` in `max uF uW`,
exactly as the target requires. Admissibility of `π` and `σ` is accepted
but not used: exhaustion needs only irreducibility.

## Actual public dependencies

All inputs are published Library theorems without extra hypotheses,
imported by Lean module name. The `lean_check` inspection below reports only
the standard axioms for the final theorem, so no input on this route rests
on a proof hole or a new axiom.

| Lean name | Module | Role |
| --- | --- | --- |
| `Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence_of_exhaustion_classification` | `Langlands.Representation.RankinSelberg.LanglandsPairEpsilonBlockExistence` | Reduction to `hex` and `hcl`, with the block input proved |
| `Langlands.RankinSelberg.squareIntegrableDataEpsilonExistence` (used inside the above) | same | Every pair of blocks of two square-integrable data has a JPSS epsilon factor: essentially square-integrable blocks are generic, and `genericSymmetricEpsilonData_isPadic` supplies the factor in either rank order |
| `Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence_of_classification` (used inside the above) | `Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceStatement` | The published conditional reduction of the target |
| `Langlands.RankinSelberg.langlandsPairEpsilonFactorOfClassification` (used inside the above) | `Langlands.Representation.RankinSelberg.LanglandsFactorDescent` | Constructs the certified pair from irreducibility, exhaustion, classification and block existence |
| `Langlands.Classification.squareIntegrableLanglandsExhaustion` | `Langlands.Representation.Classification.SquareIntegrableLanglandsExhaustionProof` | Every positive-rank irreducible smooth representation is the Langlands head of a square-integrable datum |
| `Langlands.Classification.squareIntegrableLanglandsClassification` | `Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof` | Irreducible quotients of two such data are isomorphic exactly when their blocks match up to permutation |

The paired Markdown of each module documents its own proof route and sources.

## Provenance

This proof is a derived assembly of published results; it makes no new
literature claim. The mathematical content of the target is Henniart 2002,
§2.8, printed page 596 (source `henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`): the
Langlands classification by essentially square-integrable blocks and the
product formula `ε(s, π × π') = ∏_(i,j) ε(s, π_i × π'_j, ψ)`. The statement's
Markdown records this source audit. As there, no comparison with the
analytic JPSS factor of a generic pair is claimed.

## Lean checks

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, module
`Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceProof`,
declaration `Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence`:

- 0 errors and 0 warnings;
- a theorem with universe parameters `uF`, `uV`, `uW`;
- axioms `propext`, `Classical.choice`, `Quot.sound`.
