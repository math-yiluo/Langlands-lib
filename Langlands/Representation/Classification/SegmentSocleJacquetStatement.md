# Two-block Jacquet modules of segment socles

Author: Worker 756.

`Langlands.Classification.SegmentSocleJacquetFormula.{uF,uV} F T` is a proposition
definition. It states Zelevinsky 1980, Proposition 3.4 (printed pp.181–182, PDF pages
18–19, zero-based indices 17–18, of the registered source
`zelevinsky-1980-induced-ii`) for the unique irreducible subrepresentation of the
increasing segment induction. **This contribution does not prove the formula.** It
states the formula and adds a few elementary helper constructions.

## The statement

Fix a prime `p`, an arbitrary p-adic field `F : PadicField.{uF} p` and supplied
topological data `T : F.TopologicalData`. Let `Δ : Segment.{uV,uF} T` have
beginning `ρ = Δ.base`, length `m = Δ.length` and cuspidal rank
`r = Δ.rank`, so that `n = Δ.degree = m * r`. The field universe `uF` and the base
universe `uV` are independent, and `uV` is not saturated. Let `π` be an actual smooth
complex representation of `GL_n(F)` with carrier in `Type (max uF uV)`. The only
hypothesis on `π` is `T.IsSegmentSocle Δ π`. The proposition then asserts two
clauses.

1. **Vanishing.** Let `0 < l < n` with `¬ r ∣ l`. Then the actual normalized Jacquet
   module along the ordered split `(l, n - l)` is zero:
   `Subsingleton ((T.normalizedJacquetFunctor (BlockShape.ofPair l (n - l) …)).obj π)`.
2. **Two-block formula.** Let `0 < q < m`, so `l = q * r`. Then there exist actual
   smooth representations `π₁` of `GL_(q r)(F)` and `π₂` of `GL_((m-q) r)(F)`, both
   with carriers in `Type (max uF uV)`, satisfying the following:
   - `T.IsSegmentSocle (Δ.initial q hq) π₁`, the socle for the initial segment
     `[ρ, ν^(q-1) ρ]`;
   - `T.IsSegmentSocle (Δ.terminal q hqm) π₂`, the socle for the terminal segment
     `[ν^q ρ, ν^(m-1) ρ]`;
   - an isomorphism of smooth representations of the actual ordered block Levi
     `GL_(q r)(F) × GL_((m-q) r)(F)`:
     `(T.normalizedJacquetFunctor (Δ.socleSplitShape q hq hqm)).obj π ≅
       FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)`.

The second clause asserts the existence of the shorter socles together with the
isomorphism, so it cannot hold vacuously. It does not quantify over shorter socles
that might not exist. The isomorphism is one in the category `SmoothRep` of the
Levi `(Δ.socleSplitShape q hq hqm).Levi F.Carrier = ∀ i, GL_(size i)(F)`. Both sides
have carriers in `Type (max uF uV)`. The Jacquet functor uses the Levi topology
`T.leviTopology`. That topology is the product topology of the blocks, which is
also the topology used by `FiniteTensor.externalFunctor`. No Jacquet object is
defined here and no isomorphism is taken as structure data.

## Lean helpers

The file imports `SegmentHeadJacquetStatement`, which publishes the helpers of the
head-side analogue (Zelevinsky 9.5, task 262f1d44-0ca4-44b0-a7ca-8801d8831522).
They are reused rather than duplicated:

- `GeneralLinear.BlockShape.ofPair a b ha hb h` is the block shape of `GL_n` with
  `length = 2` and `size = ![a, b]`. Its standard parabolic is the actual upper
  block-triangular `P_(a,b)`.
- `Segment.initial Δ q hq` is the segment with base `Δ.base` and length `q`, i.e.
  `[ρ, ν^(q-1) ρ]` (`initial_member`).
- `Segment.terminal Δ q hqm` is the segment with base `Δ.member q = Δ.base.twist q`
  and length `m - q`, i.e. `[ν^q ρ, ν^(m-1) ρ]` (`terminal_member`,
  `terminal_last`).
- Both subsegments have rank `Δ.rank`, and their degrees are `q * r` and
  `(m - q) * r` (`initial_degree`, `terminal_degree`, both `rfl`).

The published head-side `splitShape` and `splitFactors` put the terminal segment
first, which is the order of 9.5. They are therefore not used here. This file adds
the initial-first counterparts. All of them are internal constructions, and none
corresponds to a separate assertion of the source.

| Declaration | Content |
| --- | --- |
| `Segment.initial_degree_add_terminal_degree` | `q r + (m - q) r = m r`, from the published `terminal_degree_add_initial_degree`. |
| `Segment.socleSplitShape Δ q hq hqm` | `BlockShape.ofPair` of `GL_(m r)` with sizes `((Δ.initial q hq).degree, (Δ.terminal q hqm).degree)`, i.e. `(q r, (m - q) r)`. |
| `Segment.socleSplitShape_eq_ofPair` | `socleSplitShape` is literally the shape `ofPair (q r) (n - q r)` used in the vanishing clause at `l = q r`. So both clauses concern the same family of splits `(l, n - l)`. |
| `Segment.socleSplitFactors Δ q hq hqm π₁ π₂` | The dependent family `Fin.cons π₁ (Fin.cons π₂ finZeroElim)` of block factors of `socleSplitShape`: block `0` carries `π₁` and block `1` carries `π₂`. |

The sizes of `socleSplitShape` are definitionally the degrees of the two subsegments.
This makes `π₁` and `π₂`, which live on the groups required by `IsSegmentSocle`,
directly the block factors without any cast.

## Source correspondence and notation

The source, 3.4, takes `ρ ∈ Irr G_m` cuspidal and `ρ' = ν^(k-1) ρ`, so
`⟨Δ⟩ ∈ Irr G_n` with `n = k m`.

- The source's `m` is the cuspidal rank, our `r = Δ.rank`.
- The source's `k` is the number of elements of the segment, our `m = Δ.length`.
  Section 3.1 instead writes `ρ' = ν^k ρ` with `k ≥ 0`; we follow the convention
  of 3.4.
- The source's `p` in `l = m p` is our `q`, so `l = q r`.
- The source's `⟨Δ⟩` is our `π`, and `⟨[ρ, ν^(p-1) ρ]⟩` and `⟨[ν^p ρ, ρ']⟩` are
  our `π₁` and `π₂`.
- The source's `r_{(l,n-l),(n)}` is our
  `T.normalizedJacquetFunctor (BlockShape.ofPair l (n - l) …)`.

3.4 states that `r_{(l,n-l),(n)}(⟨Δ⟩) = 0` if `m ∤ l`, and that
`r_{(l,n-l),(n)}(⟨Δ⟩) = ⟨[ρ, ν^(p-1) ρ]⟩ ⊗ ⟨[ν^p ρ, ρ']⟩` if `l = m p`.
No erratum to Zelevinsky 1980 was found among the registered literature or the
Library notes.

**Factor order.** The first block, of size `l = q r`, carries the socle of the
initial segment. The second block, of size `n - l = (m - q) r`, carries the socle of
the terminal segment. This order was checked against the printed page, not assumed.
It is the left-to-right order of the tensor product in the displayed formula of
3.4. The proof on pp.181–182 confirms it: it writes
`r_{(l,n-l),(n)}(⟨Δ⟩) = σ₁ ⊗ σ₂` with `σ₁ ∈ Irr G_l` and `σ₂ ∈ Irr G_(n-l)`. It then
finds that `σ₁` has cuspidal Jacquet module `ρ ⊗ νρ ⊗ … ⊗ ν^(p-1) ρ` and `σ₂` has
`ν^p ρ ⊗ … ⊗ ρ'`, and concludes `σ₁ = ⟨[ρ, ν^(p-1) ρ]⟩` and `σ₂ = ⟨[ν^p ρ, ρ']⟩`
by 3.1. The Library's `BlockShape` numbers its blocks consecutively from the upper
left (`BlockShape.indexEquiv`). The source's 1.1 likewise embeds
`G_α = G_(n_1) × … × G_(n_r)` block-diagonally with first block `{1, …, n_1}`, and
its 1.3 takes the parabolic `P_β` to be upper block-triangular. By contrast, the head formula 9.5 uses the
split `(n - l, l)` and puts the terminal segment first. That is a different
representation and a different formula, stated separately in
`SegmentHeadJacquetStatement`.

**Jacquet normalization.** Section 1 of the source uses the normalized functors
`r_{β,α}` of Bernstein–Zelevinsky 1977 for the standard upper block-triangular
parabolic. The Library's `T.normalizedJacquetFunctor B` takes coinvariants under
the unipotent radical of the upper block parabolic of `B`. The Levi then acts by the
inverse half modulus times the action of the embedded block-diagonal matrix
(`normalizedJacquet_mk_eq_inv_halfModulus`, with factor `(T.leviHalfModulus B m)⁻¹`,
where `T.leviModulus` of the shape `(1, 1)` is `|a| / |b|` on `diag(a, b)`). The two
normalizations agree. As a consistency check, take `r = 1`, `m = 2`,
`ρ = ν^(-1/2)` and `q = 1`. The source's Example 3.2 gives
`⟨Δ⟩ = ν^(1/2) · ρ(det) = 1`, the trivial character of `GL_2`. In the Library's
normalization, `ν^(-1/2) × ν^(1/2)` is the space of smooth functions on `B \ GL_2`,
whose unique irreducible subrepresentation is the constants. The normalized
Jacquet module of the trivial character along the Borel is
`δ_B^(-1/2) = ν^(-1/2) ⊗ ν^(1/2)`. That character is exactly the right-hand side, the
socles of the one-element segments `[ν^(-1/2)]` and `[ν^(1/2)]` in this order.

**Increasing-induction socle.** `T.IsSegmentSocle Δ π` says that there is an actual
supercuspidal representative `A` of `ρ` such that `π` is the irreducible socle of the
increasing induction `T.segmentInduced A.obj m _ = i(ρ, νρ, …, ν^(m-1) ρ)`. That is,
`π` is irreducible and embeds, and every injective intertwiner from an irreducible
representation with carrier in `Type (max uF uV)` has the same image
(`Classification.IsIrreducibleSocle`). This is the
source's characterization of `⟨Δ⟩` in 3.1 as "the unique irreducible submodule of
`ρ × νρ × … × ρ'`". Section 3.1 equivalently describes `⟨Δ⟩` as the unique
irreducible quotient of the decreasing product `ρ' × ν^(-1) ρ' × … × ρ`, or by its
cuspidal Jacquet module `ρ ⊗ νρ ⊗ … ⊗ ρ'`. Those descriptions are not used as
hypotheses, and their equivalence with the socle form is not asserted here.

The hypothesis must not be confused with `T.IsSegmentHead`, the strong head of the
same increasing induction. That is the source's `⟨Δ⟩^t` of 9.1, whose two-block
formula is the separate statement `SegmentHeadJacquetFormula`. No analytic
assumption occurs.

## Scope

- **Endpoints.** Only proper splits `0 < l < n` are stated. The source's sum
  `c(⟨Δ⟩) = ⟨∅⟩ ⊗ ⟨Δ⟩ + ρ ⊗ ⟨[νρ, ρ']⟩ + … + ⟨Δ⟩ ⊗ ⟨∅⟩` (see 1.7) also contains
  the endpoint terms `⟨∅⟩ ⊗ ⟨Δ⟩` and `⟨Δ⟩ ⊗ ⟨∅⟩`, for `l = 0` and `l = n`. Those
  are the trivial identity cases, with an empty segment and a block `GL_0`. They are
  outside this unit. `Segment` requires positive length and `BlockShape` requires
  positive block sizes, so no empty segment or zero-rank block appears.
- **Length one.** If `m = 1` then every proper `l` satisfies `0 < l < r`, so
  `r ∤ l`. The vanishing clause asserts that all proper Jacquet modules vanish, and
  the formula clause is vacuous because no `q` satisfies `0 < q < 1`.
- No derivative, genericity or exponent conclusion is part of this unit. Theorem 3.5
  (derivatives of `⟨Δ⟩`) is not stated here.

## Unproved formula

This file proves no part of `SegmentSocleJacquetFormula`. An exact independent proof
must establish the actual Jacquet vanishing and isomorphism. The route of 3.4
(printed pp.181–182) combines the following ingredients:

- vanishing of the Jacquet module of the cuspidal induction `ρ × νρ × … × ρ'`
  along `(l, n - l)` unless `r ∣ l` (the proof cites Bernstein–Zelevinsky 1977,
  2.13(a), or 1.6), together with exactness of the Jacquet functor, to pass to the
  subrepresentation `⟨Δ⟩`;
- transitivity of Jacquet functors (1.1(c));
- nonvanishing of the further Jacquet module down to `(r, …, r)` on every
  composition factor of the two-block Jacquet module, which the proof deduces from
  1.10;
- the one-term full cuspidal Jacquet module `ρ ⊗ νρ ⊗ … ⊗ ρ'` of `⟨Δ⟩` (3.1), which
  forces the two-block Jacquet module to be irreducible, hence of the form
  `σ₁ ⊗ σ₂`;
- the Jacquet module of an external tensor product (1.5(a));
- recognition of the shorter socles from their full cuspidal Jacquet modules (3.1
  for the shorter segments).

Each of these is a separate obligation, and none is supplied or assumed here. Only
the published definitions are imported: `Segment`, `CuspidalDatum.twist` (through
`Segment.member`), `IsSegmentSocle`, `normalizedJacquetFunctor`,
`FiniteTensor.externalFunctor` and `BlockShape`/`Levi`, together with the
head-side helpers named above.
