# Reduction of the complementary series to the character-limit theorem

Authors: Worker 607 (Lean proof, carried over from the shared draft of Task 5219)
and Worker 5219 (refresh against the current Library and Markdown).

The module `Langlands.Representation.Classification.TadicComplementaryEndpointBridge`
derives Tadić's complementary-series proposition
`Langlands.Classification.ComplementarySeriesUnitarity` (Tadić 1986,
Proposition 2.9) from the character-limit theorem
`Langlands.UnitaryCharacterLimitSubquotientsStatement`. The character-limit
theorem is an explicit hypothesis `hlimit` of both main theorems, so nothing
here is proved unconditionally. The universes `uF` (field) and `uV`
(representation spaces) are independent. `hlimit` is used at the universe
pair `{uF, max uF uV}`, the universes of the actual general linear group and of
the representations.

## `complementaryEndpoint_of_characterLimit`

Fix `n > 0`, an irreducible unitarizable smooth representation `A` of
`GL_n(F)`, a real `a > 0`, and assume that `complementaryProduct F T hn A s` is
irreducible for every `s ∈ (-a, a)`. Equip `GL_{2n}(F)` with its Borel
structure. Then for every regular Haar measure `μ` that is also right invariant,
every irreducible subquotient `τ` of `complementaryProduct F T hn A a` is
unitarizable.

Proof, as implemented:

1. The private lemma `approachEndpoint` shows that `x k = a - a / (k + 1)` lies
   in `(-a, a)` and tends to `a`.
2. `A` is admissible by the first component of
   `CuspidalSupport.cuspidalEmbedding`. Hence every
   `π k = complementaryProduct F T hn A (x k)` and the end point
   `ρ = complementaryProduct F T hn A a` are admissible
   (`complementaryProduct_admissible`).
3. Each `π k` is irreducible by hypothesis. It is unitarizable by the
   open-interval theorem `complementaryProduct_unitarizableOnInterval`.
4. `ρ` has finite length (`complementaryProduct_finiteLength`).
5. For every test function `f`, the distribution characters of `π k` at `f`
   converge to that of `ρ`. This follows from the continuity of
   `s ↦ Character.distribution μ (complementaryProduct … s) f`
   (`continuous_complementaryProduct_distribution`), composed with the
   convergence `x k → a`.
6. Applying `hlimit` to `GL_{2n}(F)`, `μ`, the sequence `π`, the end point `ρ`
   and these facts gives unitarizability of `τ`.

The admissibility, finite-length and continuity lemmas are published in
`TadicComplementaryEndpointHelpers` and `TadicComplementarySeriesUnitarityProof`.

## `exists_generalLinear_biHaar` (private)

For `m > 0`, `GL_m(F)` with its Borel structure carries a Haar measure that is
regular and right invariant. Write `m = k + 1` and take the Library's
`RankinSelberg.generalLinearHaar F.Carrier k`, whose Haar, regularity and
right-invariance instances are found by instance search.

## `complementarySeriesUnitarity_of_characterLimit`

`UnitaryCharacterLimitSubquotientsStatement.{uF, max uF uV} →
ComplementarySeriesUnitarity.{uF, uV} F T`. The open-interval clause is
`complementaryProduct_unitarizableOnInterval`. For the end-point clause, choose
a measure with `exists_generalLinear_biHaar` at rank `2 * n` and apply
`complementaryEndpoint_of_characterLimit`. The target statement is used
exactly as published, with no extra hypotheses besides `hlimit`.
