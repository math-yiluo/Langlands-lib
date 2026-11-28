# The positive-depth step of BK93 (8.1.5) from its cases

Module `Langlands.BushnellKutzko.PositiveDepthCharacterStepReduction` states four propositions
used in the positive-depth argument of the proof of Bushnell–Kutzko (8.1.5) (BK93, printed
pp. 270–275, PDF pp. 282–287), and proves (`positiveDepthCharacterStepReduction`) that these four
propositions, together with the restriction properties `SimpleCharacterRestrictionStatement` of
simple characters, imply `PositiveDepthCharacterStepStatement` (module
`SplitTypeExistenceSteps`). Character propagation (proposition 1, BK93 (8.1.7)) is used in the
coarse-chain branch of the proof below, and in the source also in the derivation of the lowering
inputs (8.1.10)–(8.1.15). Propositions 2 and 3 treat the nonfundamental and the nonsplit
derived stratum, and proposition 4 the coarse lattice chain. The coprime split branch needs no
further proposition: it uses Definition (8.1.3) (`IsUnequalPositiveSplitType`). The four
propositions and `SimpleCharacterRestrictionStatement` are not proved in this module.

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Mathematics Studies 129 (1993), proof of (8.1.5), case `m ≥ 1`, with
(8.1.7)–(8.1.15) and Definition (8.1.3).

## Notation

As in `SplitTypeExistenceSteps`: `F` is a nonarchimedean local field, `ψF` satisfies
`IsBKAdditiveCharacter`, `π` is a smooth complex representation of `GL_N(F)` (`N` is the Lean
`n`), and a stratum `S = [𝔄, n, m, β]` has level `S.n`, `m = S.r`, lattice chain `S.chain`
with period `e(𝔄)`, and element `β = S.b`. For a simple stratum with `m = j + 1 ≥ 1`:

- `C(𝔄, k, β)` is `simpleCharacters ψF S.chain S.n S.b q.tail k`, a set of characters of
  `H^{k+1}(β, 𝔄) = simpleHGroup S.chain S.n S.b q.tail (k + 1)`, for a defining-sequence choice
  `q`;
- `E = F[β]` is `elementAlgebra S.b`, a field by `hS.1.1.fst.toField`; `𝔅` is the hereditary
  `𝔬_E`-order of the centralizer chain `S.chain.subfieldChain E _`, with period
  `e(𝔅 | 𝔬_E)`;
- for a tame corestriction `s` relative to `E/F` and `c ∈ 𝔓^{-m}`
  (`c : S.chain.endFiltration (-m)`), the derived stratum `[𝔅, m, m − 1, s(c)]` is
  `S.chain.corestrictedStratum _ s m c` (module `UnequalPositiveSplitType`);
- `traceTwistedCharacter ψF hψ S q j θ c`, defined here, is the character `ϑ = θ ψ_c` of
  `H^m(β, 𝔄)`: the product of `θ` and the restriction of
  `ψ_c = filtrationTraceCharacter S.chain ψF hψ _ c.2` along `H^m(β, 𝔄) ≤ U^m(𝔄)`. This is the
  character `θ ψ_c` of Definition (8.1.3) and of BK93, printed p. 270.
- `π` contains a character `χ` of a subgroup of `Aut_F(F^N)` (`ContainsAutCharacter π χ`) if
  some nonzero vector is an eigenvector of `π` with eigencharacter `χ`, through
  `Matrix.GeneralLinearGroup.toLin`.

A smaller depth means `T.r · e(S) < S.r · e(T)` in `ℤ`, i.e. `T.r / e(T) < S.r / e(S)`.

## The four propositions

1. `PositiveDepthCharacterPropagationStatement` — BK93 (8.1.7) for characters. Let
   `[𝔄, n, m, β]` be simple with `m = j + 1`, `θ ∈ C(𝔄, m − 1, β)`, `c ∈ 𝔓^{-m}`, and let `π`
   be irreducible and contain `ϑ = θ ψ_c`. If `K ≤ U^m(𝔄)` is a subgroup and `χ` a character
   of `K` agreeing with `ϑ` on `K ∩ H^m(β, 𝔄)`, then `π` contains `χ`. BK93 state (8.1.7)
   for an open subgroup `𝒪 ≤ U^m(𝔄)` and an irreducible representation `ρ` of `𝒪`; for a
   character, openness is not needed: `ϑ` is trivial on some `U^k(𝔄) ⊆ H^m(β, 𝔄)` normal in
   `U^m(𝔄)`, so `χ` extends to the open subgroup `K · U^k(𝔄)` by `χ(x u) = χ(x)`, and that
   extension agrees with `ϑ` on `K U^k(𝔄) ∩ H^m(β, 𝔄)`.
2. `NonfundamentalDerivedCharacterStatement` — BK93 (8.1.10)–(8.1.13). With `θ`, `c` as in 1
   and a tame corestriction `s`, if `[𝔅, m, m − 1, s(c)]` is not fundamental, then every
   irreducible `π` containing `θ ψ_c` contains a simple character of a simple stratum `T` of
   smaller depth (`ContainsSimpleCharacter ψF π T`). In the source, `T` is `[𝔄', n', m', β]`
   with `𝔄'` from (2.3.1) and `m'/e(𝔄') < m/e(𝔄)` by (8.1.10)(ii); BK93 phrase this as a
   contradiction with a minimal choice of `m/e(𝔄)`.
3. `NonsplitDerivedCharacterStatement` — BK93 (8.1.14)–(8.1.15). The same conclusion when the
   derived stratum is nonsplit fundamental; this is (8.1.15) for irreducible `π`.
4. `CoarseChainCharacterStatement` — BK93, printed pp. 274–275. Let `[𝔄, n, m, β]` be simple
   with `m = j + 1` and `d = gcd(m, e(𝔅 | 𝔬_E)) > 1`. For every `θ ∈ C(𝔄, m, β)` there are a
   simple stratum `T` with `0 ≤ T.r < m` and the same depth, a defining-sequence choice for
   `T`, and `θ' ∈ C(T)` (a character of `H^{T.r+1}(T)`), such that
   `H^{T.r+1}(T) ≤ U^{m+1}(𝔄)` and `θ'` agrees with `θ` on `H^{m+1}(β, 𝔄) ∩ H^{T.r+1}(T)`. In
   the source, `T = [𝔄', n/d, m/d, β]` on the coarser chain `{L_{id}}` and `θ'` is the
   character given by (3.6.1). This proposition concerns no representation: the passage to
   `π` is made by (8.1.7) in the proof below, as in the source. It is stated for an arbitrary
   `F`-vector space `V`.

In 2 and 3 the tame corestriction is arbitrary. BK93 fix one satisfying (1.3.5); any two tame
corestrictions differ by a unit of `𝔬_E` (`tameCorestriction`, second clause), and
fundamentality and splitness of `[𝔅, m, m − 1, s(c)]` do not change under such a scaling.

`PositiveDepthCharacterStepReductionStatement` is the implication
`SimpleCharacterRestrictionStatement → 1 → 2 → 3 → 4 → PositiveDepthCharacterStepStatement`,
at the universes of `PositiveDepthCharacterStepStatement` (field `uF`, representation carriers
`uπ`, `uρ`; the vector space of `SimpleCharacterRestrictionStatement` and of 4 is `F^N`, in
universe `uF`).

## The proof

`positiveDepthCharacterStepReduction` proves the target by induction on a natural-number bound
`k > S.r.toNat` for the integer stratum index `m = S.r` (not on the depth `m / e(𝔄)`, which the
coarse-chain branch keeps fixed while lowering `m`), for all simple strata at once: if `π`
contains a simple character
of a simple stratum `S` with `S.r > 0`, then `π` contains a split type of level `(x, y)` or a
simple character of a stratum of smaller depth than `S`. Let `m = j + 1`.

- **From `θ` to `θ̃ ψ_c`** (BK93, printed p. 270; `exists_traceTwistedCharacter_of_contains`).
  Let `π` contain `θ ∈ C(𝔄, m, β)`. By clause 4 of `SimpleCharacterRestrictionStatement`,
  applied to the simple stratum `[𝔄, n, 0, β]` (`S.atDepthZero`, simple by
  `Stratum.isSimple_atDepthZero`) and `m < n`, restriction maps `C(𝔄, m − 1, β)` onto
  `C(𝔄, m, β)`, so `θ = θ̃ | H^{m+1}` for some `θ̃ ∈ C(𝔄, m − 1, β)`. The commutators of `H^m(β, 𝔄)` lie in `H^{m+1}(β, 𝔄)`
  (`simpleStratumGroupProperties`), and `H^m ∩ U^{m+1}(𝔄) = H^{m+1}` has finite index in
  `H^m`. So the representation `θ̃^{-1} ⊗ π` of `H^m` on the finite-dimensional span of the
  `H^m`-translates of a `θ`-eigenvector has a common eigenvector (`exists_eigencharacter`,
  from `Module.End.exists_eigenvalue`), whose eigencharacter `χ` is trivial on
  `H^m ∩ U^{m+1}(𝔄)`. Then `χ` factors through `H^m / (H^m ∩ U^{m+1}) ↪ U^m(𝔄)/U^{m+1}(𝔄)`,
  extends to a character of `U^m(𝔄)/U^{m+1}(𝔄)` (`exists_complexCharacter_extension`), and by
  additive duality (`additiveDuality`, clause (c)) is `ψ_c` for some `c ∈ 𝔓^{-m}`. Thus `π`
  contains `θ̃ ψ_c`.
- **The cases of the derived stratum** (`exists_derivedStratum_cases`). Take any tame
  corestriction `s` (`tameCorestriction`). Then `[𝔅, m, m − 1, s(c)]` is not fundamental, or
  nonsplit, or split with `gcd(m, e(𝔅 | 𝔬_E)) = 1`, or `gcd(m, e(𝔅 | 𝔬_E)) > 1`. A fundamental
  stratum that is not split is nonsplit (`isNonsplit_of_not_isSplit`): the reduced
  characteristic polynomial is monic of positive degree, and a monic polynomial over a field
  without a factorization into two coprime nonconstant monic factors is a power of one monic
  irreducible polynomial (`PureApproximation.exists_eq_pow_of_not_two_factors`).
- **Not fundamental, or nonsplit**: propositions 2 and 3 give a contained simple character of
  smaller depth.
- **Split, `gcd(m, e(𝔅 | 𝔬_E)) = 1`**: `(H^m(β, 𝔄), θ̃ ψ_c)` is a split type of level
  `(n/e(𝔄), m/e(𝔄))` by Definition (8.1.3) (`IsUnequalPositiveSplitType`). The pair in matrix
  coordinates is `K = toLin⁻¹(H^m)` with the character `θ̃ ψ_c ∘ toLin` on a one-dimensional
  space; it is smooth because `π`'s eigenvector is fixed by an open subgroup, and `π` contains
  it through the eigenvector (`exists_containsType_of_containsAutCharacter`).
- **`gcd(m, e(𝔅 | 𝔬_E)) > 1`**: proposition 4 gives `T`, of the same depth with `T.r < m`, and
  `θ' ∈ C(T)`. Proposition 1, applied to `K = H^{T.r+1}(T) ≤ U^{m+1}(𝔄)` and `χ = θ'`, shows
  that `π` contains `θ'`: on `K ∩ H^m(β, 𝔄) ⊆ H^{m+1}(β, 𝔄)`, `ψ_c` is trivial and `θ̃` is `θ`,
  which agrees with `θ'`. Since the depths agree and `S.r > 0`, `T.r > 0`. Since
  `T.r < S.r < k + 1`, the induction hypothesis applies to `T` (the integer index decreases
  while the depth is unchanged) and gives a split type or a stratum of smaller depth than `T`,
  hence than `S`, because the periods are positive (`depth_lt_of_eq_of_lt`).

The helper `exists_derivedStratum_cases` is compiled with `maxHeartbeats 1000000`: elaborating
its statement, which names three predicates on a stratum over `F[β]`, uses most of the default
limit.
