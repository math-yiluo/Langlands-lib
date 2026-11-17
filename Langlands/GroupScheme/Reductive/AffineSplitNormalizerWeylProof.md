# Proof: normalizer points of a split maximal torus map onto the Weyl group

Worker 4348 and Worker 5397 (Task 6589).

`Langlands.GroupScheme.affineSplitNormalizerWeyl : AffineSplitNormalizerWeylStatement.{u}` proves
the published statement
[`Reductive.AffineSplitNormalizerWeylStatement`](AffineSplitNormalizerWeylStatement.md)
(Conrad, *Reductive group schemes*, Example 6.4.3). The statement's Lean/Markdown pair is
unchanged. The proof uses the axioms `propext`, `Classical.choice` and `Quot.sound`. It
introduces the binders and hypotheses of the statement, then proves the four clauses from
four helper modules:

| Clause | Result used | Module |
| --- | --- | --- |
| 1. every `w ∈ P.weylGroup` is induced by some `n ∈ G(S)` | `AffineSplitReflection.weylGroup_induced` | [`AffineSplitReflectionRepresentatives`](AffineSplitReflectionRepresentatives.md) (Worker 5397) |
| 2. normalizer points induce Weyl elements | `AffineSplitNormalizerWeyl.exists_weylGroup_of_mem_normalizerPoints` | [`AffineSplitNormalizerWeylClauses`](AffineSplitNormalizerWeylClauses.md) (Worker 4348) |
| 3. centralizer points are torus points | `AffineSplitNormalizerWeyl.exists_eq_of_mem_centralizerPoints` | [`AffineSplitNormalizerWeylClauses`](AffineSplitNormalizerWeylClauses.md) |
| 4. over a domain, a finite subgroup of normalizer points induces all of `W(P)` | `AffineSplitReflection.exists_reflection_representatives` and `AffineSplitNormalizerWeyl.exists_finite_subgroup_of_representatives` | [`AffineSplitNormalizedRepresentatives`](AffineSplitNormalizedRepresentatives.md) (Worker 5397), [`AffineSplitNormalizerWeylFinite`](AffineSplitNormalizerWeylFinite.md) (Worker 4348) |

## The proof

After `intro R _ _ G hG I _ i J P hi hmax hP hfree Induces` the goal is the conjunction of the
four clauses. Each clause uses the statement's local relation `Induces`.

- **Clause 1.** `weylGroup_induced R G hG I i J P hi hmax hP hfree` has the same hypotheses as the
  statement and concludes `∀ w ∈ P.weylGroup, ∃ n, ∃ σ, IsNormalizingPoint i n σ ∧ …`, with the
  body of `Induces` written out literally. It is used as is. In outline, its proof builds
  representatives of the reflections from global root parametrizations. Their normalizing
  scalars exist at every localization `R_𝔭`, and they glue by descent along the localizations
  at primes. Products of these representatives then give every element of the Weyl group.
  The module's Markdown has the details.
- **Clause 2.** `exists_weylGroup_of_mem_normalizerPoints hG i hi hmax hP hn` concludes
  `∃ w ∈ P.weylGroup, Induces i n w`. The helper relation `AffineSplitNormalizerWeyl.Induces i n w`
  unfolds definitionally to the statement's `Induces n w`. Over the connected base, conjugation by
  `n` acts on the torus by one integer matrix. The Weyl element is found on the fibre over a
  residue field `R ⧸ 𝔪` and carried back to `P`.
- **Clause 3.** `exists_eq_of_mem_centralizerPoints hG i hi hmax hn` gives the torus point. The
  centralizer of a fibrewise maximal split torus is its range
  (`splitTorusCentralizer_eq_range_of_fibrewiseMaximal`).
- **Clause 4.** The domain hypothesis is not used. `exists_reflection_representatives hG i hi
  hmax hP hfree` gives points `n a` for every root `a`. Each `n a` induces the reflection
  `s_a`, and `n a * n a = t ≫ i.hom.hom` for a torus point `t` with `t * t = 1`. The value is
  `a^∨(-1)`. These are exactly the hypotheses `hn` and `hsq` of
  `exists_finite_subgroup_of_representatives`. That theorem also needs `Finite J` and
  `P.IsReduced`, the first two components of `hP : IsFibrewiseRootDatumOf I G i P`. It returns
  `H ≤ normalizerPoints i` with `Finite H` and `∀ w ∈ P.weylGroup, ∃ m ∈ H, Induces i m w`. The
  finiteness proof uses the Coxeter presentation of `W(P)`, obtained via a rational root
  pairing. It shows that the Coxeter relations hold among the `n b` modulo torsion torus points,
  using a sign argument on the torsion-free quotient of `T(R)`. A Schreier argument then gives
  finiteness. The module's Markdown has the details.

The instance `IsAffineHom G.X.hom` is taken from `hG.isAffineHom` as in the statement, and
`classical` supplies `DecidableEq I`.

## Files

Besides this pair, the proof needs the helper modules
`AffineSplitNormalizerWeylClauses`, `AffineSplitNormalizerWeylFinite`,
`AffineSplitReflectionRepresentatives` and `AffineSplitNormalizedRepresentatives` (Lean and
Markdown). They are also submitted separately, as candidates abc3f328, 30a01151, 5549a2a7 and
3b1b1c57. All other imports are published Library modules.
