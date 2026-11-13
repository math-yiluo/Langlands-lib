# Local isobaric sums for `GL_n` over a p-adic field

Author: Worker 3657. Definition module of a statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** The module `Langlands.Representation.Classification.IsobaricSum`
contains one definition and one immediate lemma:

- `Langlands.PadicField.TopologicalData.IsIsobaricSum`, a relation saying that
  a representation `τ` of `GL_N(F)` is the isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` of
  representations `π_i` of `GL_(n_i)(F)`;
- `Langlands.PadicField.TopologicalData.IsIsobaricSum.isIrreducible`: such a
  `τ` is irreducible.

It is used by `Langlands.Global.CuspidalIsobaricRealizationStatement`
(`Langlands/Global/Factors/CuspidalIsobaricRealizationStatement.lean`), the
statement of Getz–Hahn (2024), Theorem 10.7.5 at the finite places. The module
records the isobaric sum only as a relation. It does not assert that an
isobaric sum exists, that it is unique, or that it is independent of choices.

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.28)–(10.31), p.283 (PDF 295); Thm 10.6.1, its notation `⊞`, Thm 10.6.2 and (10.33), p.284 (PDF 296); "isobaric sum" and Example 10.3, p.285 (PDF 297); Thm 10.6.4, p.286 (PDF 298) |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | segments (1.2.1) and Thm 1.2.2, p.369 (PDF 379); essentially square-integrable `Q(Δ)`, Def 1.2.4 and Thm 1.2.5(a), p.370 (PDF 380); Thm 1.2.5(b)–(d), p.371 (PDF 381) |

The Kudla file is the whole *Motives* Part 2 volume; its PDF page is the
printed page plus 10.

**What GH state.** In §10.6, `F` is a local field. For an irreducible
admissible essentially square-integrable `π_i` of `GL_(n_i)(F)`, GH write
`π_i = |det|^(λ_i) π_i^1` with `π_i^1` a representation of
`A_(GL_(n_i)) \ GL_(n_i)(F)` and `λ_i ∈ ℂ` ((10.29); `A_GL = ϖ^ℤ` in the
non-archimedean case, (10.28)), ordered so that
`Re(λ_1) ≥ ⋯ ≥ Re(λ_k)` (10.30). Then (p.284):

> **Theorem 10.6.1** The induced representation `I(⊗_(i=1)^k π_i^1, λ)` has a
> unique irreducible quotient `J(⊗_(i=1)^k π_i^1, λ)`.

The theorem adds that `J` determines `k` and the pairs `(π_i, λ_i)` up to a
permutation (10.32). GH continue: "Let `π_1 ⊞ ⋯ ⊞ π_k` be the irreducible
quotient `J(⊗_(i=1)^k π_i^1, λ)` of the theorem. In this notation we do not
assume that the `π_i` are arranged so that `Re(λ_1) ≥ ⋯ ≥ Re(λ_k)`, so by
definition `⊞_(i=1)^k π_i ≅ ⊞_(i=1)^k π_(τ(i))` for any permutation `τ`."
Theorem 10.6.2: every irreducible admissible representation of `GL_n(F)` is
equivalent to `⊞_i π_i` for some irreducible admissible essentially
square-integrable `π_i`. Then, for arbitrary irreducible admissible `π_i` of
`GL_(n_i)(F)` with `∑ n_i = n`: "For each `π_i` we write
`π_i = ⊞_(j=1)^(k_i) π'_(ij)` and then set
`⊞_(i=1)^k π_i = ⊞_(i=1)^k (⊞_(j=1)^(k_i) π'_(ij))`" (10.33). On p.285 this is
named "the isobaric sum of the `π_i`", which "is always irreducible". Example
10.3 on p.285 shows that `π_1 ⊞ π_2` need not be a quotient of the induced
representation of `π_1 ⊗ π_2`.

**What Kudla states.** A segment is `Δ = [σ, σ(r-1)] = {σ, σ(1), …, σ(r-1)}`
for a supercuspidal `σ`, where `σ(k) = σ ⊗ |det|^k` ((1.2.1), p.369). Theorem
1.2.2 gives the unique irreducible quotient `Q(Δ)` of the induced
representation `I(Δ)`. On p.370 Kudla notes that the representations `Q(Δ)`
are exactly the essentially square-integrable ones. Definition 1.2.4: `Δ_1`
and `Δ_2` are linked if neither contains the other and their union is a
segment; `Δ_1` precedes `Δ_2` if they are linked and `σ_2 = σ_1(k)` with
`k > 0`. Theorem 1.2.5 (pp.370–371): if `Δ_i` does not precede `Δ_j` for
`i < j`, then (a) `I(Q(Δ_1) ⊗ ⋯ ⊗ Q(Δ_r))` has a unique irreducible quotient
`Q(Δ_1, …, Δ_r)`; (b) `Q(Δ_1, …, Δ_r) ≅ Q(Δ'_1, …, Δ'_s)` exactly when the two
multisets of segments are equal; (c) every irreducible admissible
representation is some `Q(Δ_1, …, Δ_r)`.

## 2. The definition

Let `F` be a p-adic field, `T : F.TopologicalData` a realization, `k, N : ℕ`
and `n : Fin k → ℕ`. Let `π i` be smooth representations of `GL_(n i)(F)` and
`τ` one of `GL_N(F)`, all with carriers in `Type (max uF uV)`, the universe of
the Library's segment relations. Then `T.IsIsobaricSum π τ` holds when there
are multisegments `a : Fin k → Multisegment.{uV, uF} T` such that

- each `π i` is a Langlands head of `a i`: `(a i).IsLanglandsHead (π i)`;
- `τ` is a Langlands head of the multiset sum: `(∑ i, a i).IsLanglandsHead τ`.

`Multisegment T` is `Multiset (Segment T)`
(`Langlands/Representation/Classification/Segments.lean`), so `∑ i, a i` is the
union of the multisets with multiplicities. `Multisegment.IsLanglandsHead a π`
(`Langlands/Representation/Classification/LanglandsData.lean`) says that some
`SegmentProductDatum` lists the segments of `a` in an order where no earlier
segment precedes a later one, has blocks that are segment heads (Kudla's
`Q(Δ_i)`), and has `π` as the irreducible head of the normalized induced
representation of its blocks. "Irreducible head"
(`Classification.IsIrreducibleHead`,
`Langlands/Representation/Classification/ConstituentRelations.lean`) means
that `π` is an irreducible quotient and that every surjective intertwining map
onto an irreducible representation has the same kernel. This is the Library's
form of Kudla's "unique irreducible quotient" `Q(Δ_1, …, Δ_r)`.

The degree of the multisegments is not constrained in the definition. A
Langlands head of `a` is a representation of `GL_(deg a)(F)`, so the relation
forces `deg (a i) = n i` and `∑ n i = N` whenever it holds.

`IsIsobaricSum.isIrreducible` unpacks the second condition: the head relation
contains irreducibility of `τ`.

## 3. Why this is GH's isobaric sum

The match uses Kudla's theorems; none of them is asserted here.

1. **Essentially square-integrable blocks.** Let `π_1, …, π_r` be irreducible
   essentially square-integrable with `Re(λ_1) ≥ ⋯ ≥ Re(λ_r)`, and write
   `π_i ≅ Q(Δ_i)` (Kudla p.370). If `Δ_i` precedes `Δ_j`, write
   `Δ_i = [σ, σ(r_i - 1)]` and `Δ_j = [σ(k), σ(k + r_j - 1)]` with `k ≥ 1`.
   Since `Δ_j` is not contained in `Δ_i`, `k + r_j - 1 ≥ r_i`. The real
   exponent of the central character of `Q(Δ)` is the average of the real
   exponents along `Δ`. So `Re λ_j - Re λ_i = (2k + r_j - r_i)/2 ≥ (k + 1)/2 ≥ 1`.
   Hence in GH's order (10.30) no `Δ_i` precedes a `Δ_j` with `i < j`. GH's
   `I(⊗π_i^1, λ)` is the normalized induced representation
   `I(Q(Δ_1) ⊗ ⋯ ⊗ Q(Δ_r))`, and GH's `J` is Kudla's `Q(Δ_1, …, Δ_r)`: both are
   its unique irreducible quotient.
2. **Arbitrary irreducible blocks.** By Theorem 1.2.5(c) and the previous
   step, each irreducible `π_i` is `Q(a_i)` for a multisegment `a_i`, which is
   unique by Theorem 1.2.5(b). Write `a_i = {Δ_(i1), …, Δ_(ik_i)}`. Then GH's
   decomposition `π_i = ⊞_j π'_(ij)` has `π'_(ij) ≅ Q(Δ_(ij))`. By (10.33) and
   step 1, `⊞_i π_i` is `Q` of the multiset of all `Δ_(ij)`, that is
   `Q(a_1 + ⋯ + a_k)`.

So, given Kudla's Theorem 1.2.5, `T.IsIsobaricSum π τ` holds exactly when `τ`
is isomorphic to GH's `π_1 ⊞ ⋯ ⊞ π_k`. The relation is invariant under
permuting the `π_i`, as GH require, because the multiset sum is commutative.

**Why multisegments.** The Library also has GH's form of Theorem 10.6.1:
`SquareIntegrableLanglandsDatum` in `LanglandsData.lean` (Henniart's `J` for
essentially square-integrable blocks with decreasing exponents). (10.33)
pools the essentially square-integrable constituents of all `π_i` and sorts
them again. A `SquareIntegrableLanglandsDatum` has actual blocks on an ordered
block shape, so pooling and sorting would need isomorphisms between blocks.
Segments are isomorphism-class data and multisegments are unordered, so pooling
and sorting is the multiset sum.

## 4. Universes

The multisegments are `Multisegment.{uV, uF} T`, and all representations have
carriers in `Type (max uF uV)`, as in `Multisegment.IsLanglandsHead`. The
Library's classification statements in
`MultisegmentClassificationStatement.lean` (`MultisegmentHeadExistence`,
`MultisegmentHeadExhaustion`, `MultisegmentHeadClassification`) use
`Multisegment.{max uF uV, uF} T` with the same carrier universe. Taking the
parameter `uV` of `IsIsobaricSum` to be `max uF uV` gives that form. The global
statement uses `uV = uF = u`, where the two agree.

## 5. Not claimed

- existence of an isobaric sum (GH Theorems 10.6.1, 10.6.2; Kudla 1.2.5(a),
  (c); the Library statements `MultisegmentHeadExistence` and
  `MultisegmentHeadExhaustion`);
- its uniqueness up to isomorphism, or independence of the multisegments and
  their orderings (Kudla 1.2.5(b); `MultisegmentHeadClassification`);
- invariance under isomorphisms of the `π_i` or of `τ`;
- any relation with induced representations of the `π_i`. In particular this
  module does not assert a subquotient theorem such as GH Theorem 10.6.4
  (stated for essentially unitary generic `π_i`). Separately, GH Example 10.3
  shows only that an isobaric sum need not be a *quotient* of the
  representation induced from its given blocks (see §1); it does not show
  that the subquotient property fails;
- anything for archimedean fields.

## 6. Provenance

`IsIsobaricSum` is a derived formulation of GH's local isobaric sum
(Theorem 10.6.1 and (10.33)), in Kudla's segment form (Theorem 1.2.5), by the
argument of §3. The lemma `isIrreducible` is a one-line consequence of the
definition (GH p.285: the isobaric sum "is always irreducible").

The module was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, together with the statement module that
uses it.
