# The four steps of the proof of BK93 (8.1.5)

Module `Langlands.BushnellKutzko.SplitTypeExistenceSteps` states four propositions, one for each
branch of the proof of Bushnell–Kutzko (8.1.5), and proves that together they imply
`SplitTypeExistenceStatement`. The four propositions are not proved in this module.

Notation. As in BK93, `N` denotes the ambient rank (the Lean variable `n` of the statements) and
a stratum is written `[𝔄, n, m, β]`, where the level `n` is the integer `S.n` of the Lean stratum
`S` and `m` is `S.r`; the level of a stratum is independent of the rank `N`.

Throughout, `F` is a nonarchimedean local field, `N > 0`, `ψF` satisfies
`IsBKAdditiveCharacter` (trivial on `𝔭_F`, nontrivial on `𝔬_F`), and `π` is an irreducible smooth
complex representation of `GL_N(F)` with carrier in an arbitrary universe. Admissibility is not
assumed. Types are pairs `(K, ρ)` with `K ≤ GL_N(F)` and `ρ` a smooth representation with
carrier in a second arbitrary universe; `π` contains `(K, ρ)` in the sense of `ContainsType`.
Hereditary orders are given by `𝔬_F`-lattice chains `L` in `F^N`, and subgroups of
`Aut_F(F^N)` act on `π` through `Matrix.GeneralLinearGroup.toLin`.

## Containment of characters

- `ContainsAutCharacter π χ`, for a character `χ` of a subgroup `U ≤ Aut_F(F^N)`: some nonzero
  vector `v` satisfies `π(u) v = χ(u) v` for all `u ∈ U`. Since `χ` is one-dimensional, this is
  "`π | U` contains `χ`" in the sense of BK93.
- `HasUnitFiltrationOneFixedVector π L`: `π` contains the trivial character of `U^1(𝔄)`, where
  `𝔄` is the hereditary order of `L`.
- `ContainsSimpleCharacter ψF π S`, for a stratum `S = [𝔄, n, m, β]`: `S` is simple, `m ≥ 0`, and
  for some `S.DefiningSequenceChoice` `q` there is `θ ∈ C(𝔄, m, β)`
  (`simpleCharacters ψF S.chain S.n S.b q.tail m`, a character of `H^{m+1}(β, 𝔄)`) with
  `ContainsAutCharacter π θ`.

## The four steps

1. `LevelZeroTypeContainmentStatement` (BK93, proof of (8.1.5), printed pp. 267–268). If `π` has
   a nonzero `U^1(𝔄)`-fixed vector for some hereditary order `𝔄`, then `π` contains a pair
   `(K, ρ)` that is a simple type (`IsGLSimpleType ψF ρ`) or a split type of level `(0, 0)`
   (`IsLevelZeroSplitType` of the transported representation). In the source, `𝔄` is chosen
   minimal; minimality makes the factors `ϑ_i` of an irreducible `U(𝔄)/U^1(𝔄)`-constituent
   cuspidal; if they are all equivalent, `𝔄` is principal and the pair is a simple type, and
   otherwise it is a split type of level `(0, 0)`. The proposition records the conclusion as a
   disjunction and does not mention `𝔄`'s minimality. `ψF` enters only through
   `IsGLSimpleType`, whose level-zero kind does not depend on it.
2. `PositiveLevelInitialStepStatement` (printed p. 268). If `π` has no nonzero `U^1(𝔄)`-fixed
   vector for any `𝔄`, then `π` contains a split type of level `(x, x)`
   (`IsDiagonalPositiveSplitType`), or `π` contains a simple character of some simple stratum.
   In the source, `π` contains a fundamental stratum `[𝔄, n, n-1, b]` with `n ≥ 1`, "as in"
   Bushnell 1987, Theorem 2 (which is stated there for irreducible admissible representations;
   BK93 p. 268 apply the argument to the irreducible smooth `π` of (8.1.5)). A split one can be
   taken with `gcd(n, e(𝔄)) = 1`, by arguing as in Kutzko 1988 (BK93 p. 268 cite it and say a
   more general version of the argument is given later in their proof), and gives the split
   type; a nonsplit one is replaced by a simple stratum `[𝔄', n', n'-1, α]` by (2.3.4), and
   `ψ_α | H^{n'}(α, 𝔄')` lies in `C(𝔄', n'-1, α)`. The proposition allows any `m ≥ 0` in the
   second alternative.
3. `ZeroDepthCharacterStepStatement` (printed pp. 268–270, with Lemma (8.1.6)). If `π` contains
   a simple character `θ ∈ C(𝔄, 0, β)` of a simple stratum `[𝔄, n, 0, β]` (`S.r = 0`), then `π`
   contains a simple type or a split type of level `(x, 0)` (`IsPositiveZeroSplitType`). The
   source chooses `𝔄` minimal among such pairs and, by (5.1.1), (5.2.2), (5.2.14), (3.6.2) and
   (8.1.6), shows that a noncuspidal factor would give a strictly smaller order `𝔄'` with a
   contained simple character `θ' ∈ C(𝔄', 0, β)`. Strictly smaller orders have larger periods,
   which are at most `N`, so this descent stops; hence the statement holds for every contained
   `θ ∈ C(𝔄, 0, β)`.
4. `PositiveDepthCharacterStepStatement` (printed pp. 270–275, (8.1.7)–(8.1.15)). If `π` contains
   a simple character `θ ∈ C(𝔄, m, β)` of a simple stratum `[𝔄, n, m, β]` with `m ≥ 1`, then
   `π` contains a split type of level `(x, y)` with `y > 0` (`IsUnequalPositiveSplitType`), or
   `π` contains a simple character of a simple stratum `T = [𝔄', n', m', β']` with
   `m'/e(𝔄') < m/e(𝔄)`, written `T.r · e(𝔄) < S.r · e(𝔄')` in `ℤ`. In the source, `π` contains a
   character `ϑ = θ̃ ψ_c` of `H^m(β, 𝔄)` with `θ̃ ∈ C(𝔄, m-1, β)` and `c ∈ 𝔓^{-m}`, and the
   derived stratum `[𝔅, m, m-1, s(c)]` is examined. If it is not fundamental, (8.1.10)–(8.1.13)
   give a contained simple character of smaller depth; if it is nonsplit fundamental, (8.1.14)
   and (8.1.15) do. BK93 derive contradictions with the minimality of `m/e(𝔄)` in these cases;
   the proposition records the smaller depth as the second alternative. If it is split
   fundamental with `gcd(m, e(𝔅|𝔬_E)) = 1`, `(H^m(β, 𝔄), ϑ)` is a split type of level
   `(n/e(𝔄), m/e(𝔄))`. If `d = gcd(m, e(𝔅|𝔬_E)) > 1`, the coarser chain `{L_{id}}` carries a
   contained simple character `θ' ∈ C(𝔄', m/d, β)` of the same depth (printed pp. 274–275), and
   the argument is repeated; `m` decreases, so the statement follows by induction on `m`.

`SplitTypeExistenceReductionStatement` is the implication from the four steps, each at the
universes `uF, uπ, uρ`, to `SplitTypeExistenceStatement.{uF, uπ, uρ}`.

## Proof of the reduction

`splitTypeExistenceReduction` proves `SplitTypeExistenceReductionStatement`. Assume `π` contains
no simple type.

- If `π` has a nonzero `U^1(𝔄)`-fixed vector for some `L`, step 1 gives a contained simple type,
  which is excluded, or a contained split type of level `(0, 0)`. The level `(0, 0)` witness
  enters the first disjunct of `IsGLZeroSecondLevelSplitType`, which is the second disjunct of
  `IsGLSplitType`.
- Otherwise step 2 gives a contained split type of level `(x, x)`, an `IsGLSplitType` by the first
  disjunct of `IsGLPositiveLevelSplitType`, or a contained simple character of a simple stratum
  `S`.
- For contained simple characters, induction on `scaledDepth n S = m · (N! / e(𝔄))`, a natural
  number (here `m = S.r` and the Lean argument `n` is the rank `N`). If `m = 0`, step 3 gives a
  contained simple type, which is excluded, or a split type of level `(x, 0)`, which enters the
  second disjunct of `IsGLZeroSecondLevelSplitType`. If `m ≥ 1`, step 4 gives a split type of
  level `(x, y)`, which enters the second disjunct of `IsGLPositiveLevelSplitType`, or a simple
  stratum `T` with a contained simple character and `T.r · e(S) < S.r · e(T)`. The period of a
  lattice chain in `F^N` is at most `N` (`LatticeChain.period_le_card`, module
  `NormalizedLevelExistenceProof`), so it divides `N!`, and `scaledDepth_lt` turns the
  inequality into `scaledDepth n T < scaledDepth n S`. The induction hypothesis applies to `T`.

## Sources

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), Theorem (8.1.5), printed p. 267, proof pp. 267–275 (PDF pp. 279–287), with Definitions
(8.1.1)–(8.1.4), printed pp. 266–267 (PDF pp. 278–279). Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*, J.
reine angew. Math. 375/376 (1987), 184–210, Theorem 2 and Theorem 2′, printed pp. 196–197 (PDF
pp. 13–14): an irreducible admissible representation contains a fundamental stratum, of positive
level when it has no level-zero vector. Literature ID `bushnell-1987-hereditary-orders-gauss-sums`,
SHA-256 `285eebfc66e11b0c4234c24e677ebac7472d49e113a3e3cd1e5e91c5ac364fa0`. Its use for an
arbitrary irreducible smooth representation in step 2 follows the argument of BK93, printed
p. 268.

P. C. Kutzko, *Towards a classification of the supercuspidal representations of GL_N*, J. London
Math. Soc. (2) 37 (1988), 265–274, Definition (2.3) and Proposition (2.4) (split elements),
printed p. 268 (PDF p. 4), and the proof of Theorem (3.2) with Proposition (3.4) and Lemmas
(3.5)–(3.6), printed pp. 270–274 (PDF pp. 6–10). Literature ID
`kutzko-1988-towards-classification-supercuspidal-gln`, SHA-256
`0ac89b0b4e85f690eec3ad1a34368a00318e1475cc8a8c5c7dccd938af63691b`. The proof of (3.2) concerns
supercuspidal representations; the coprimality condition `gcd(n, e(𝔄)) = 1` in step 2 for an
arbitrary irreducible smooth representation follows the application in BK93, printed p. 268.
