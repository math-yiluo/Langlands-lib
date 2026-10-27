# Two-block Jacquet modules of special segment heads

Author: Worker 256.

`Langlands.Classification.SegmentHeadJacquetFormula.{uF,uV} F T` is a proposition
definition stating Zelevinsky 1980, Proposition 9.5 (printed p.198, PDF page 35 of
the registered source `zelevinsky-1980-induced-ii`) for the strong head of the
increasing segment induction. **This contribution does not prove the formula.** It
states the formula and adds a few elementary helper constructions.

## The statement

Fix a prime `p`, an arbitrary p-adic field `F : PadicField.{uF} p` and supplied
topological data `T : F.TopologicalData`. Let `Δ : Segment.{uV,uF} T` have
beginning `ρ = Δ.base`, length `m = Δ.length` and cuspidal rank
`r = Δ.rank`, so that `n = Δ.degree = m * r`. The field universe `uF` and the base
universe `uV` are independent. Let `π` be an actual smooth complex representation
of `GL_n(F)` with carrier in `Type (max uF uV)`. The only hypothesis on `π` is
`T.IsSegmentHead Δ π`. The proposition then asserts two clauses.

1. **Vanishing.** Let `0 < l < n` with `¬ r ∣ l`. Then the actual normalized Jacquet
   module along the ordered split `(n - l, l)` is zero:
   `Subsingleton ((T.normalizedJacquetFunctor (BlockShape.ofPair (n - l) l …)).obj π)`.
2. **Two-block formula.** Let `0 < q < m`, so `l = q * r`. Then there exist actual
   smooth representations `π₁` of `GL_((m-q) r)(F)` and `π₂` of `GL_(q r)(F)`, both
   with carriers in `Type (max uF uV)`, satisfying the following:
   - `T.IsSegmentHead (Δ.terminal q hqm) π₁`, the head for the terminal segment
     `[ν^q ρ, ν^(m-1) ρ]`;
   - `T.IsSegmentHead (Δ.initial q hq) π₂`, the head for the initial segment
     `[ρ, ν^(q-1) ρ]`;
   - an isomorphism of smooth representations of the actual ordered block Levi
     `GL_((m-q) r)(F) × GL_(q r)(F)`:
     `(T.normalizedJacquetFunctor (Δ.splitShape q hq hqm)).obj π ≅
       FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)`.

The second clause asserts the existence of the shorter heads together with the
isomorphism, so it cannot hold vacuously. It does not quantify over shorter heads
that might not exist. The isomorphism is one in the category `SmoothRep` of the
Levi `(Δ.splitShape q hq hqm).Levi F.Carrier = ∀ i, GL_(size i)(F)`. Both sides
have carriers in `Type (max uF uV)`. The Jacquet functor uses the Levi topology
`T.leviTopology`. That topology is the product topology of the blocks, which is
also the topology used by `FiniteTensor.externalFunctor`.

## Lean helpers

All helpers are internal constructions. None corresponds to a separate assertion of
the source.

| Declaration | Content |
| --- | --- |
| `GeneralLinear.BlockShape.ofPair a b ha hb h` | The block shape of `GL_n` with `length = 2` and `size = ![a, b]`, for `0 < a`, `0 < b`, `a + b = n`. Its standard parabolic is the actual upper block-triangular `P_(a,b)`. The simp lemmas `ofPair_length`, `ofPair_size_zero` and `ofPair_size_one` hold by `rfl`. |
| `Segment.initial Δ q hq` | The segment with base `Δ.base` and length `q` (`0 < q`). Its members are `ν^i ρ` for `i < q`, i.e. `[ρ, ν^(q-1) ρ]` (`initial_member`). |
| `Segment.terminal Δ q hqm` | The segment with base `Δ.member q = Δ.base.twist q` and length `m - q` (`q < m`). Its members are `ν^(q+i) ρ` (`terminal_member`), and its end is `Δ.last = ν^(m-1) ρ` (`terminal_last`), i.e. `[ν^q ρ, ν^(m-1) ρ]`. |
| rank/degree lemmas | Both subsegments have rank `Δ.rank` (by `rfl`, since `CuspidalDatum.twist` keeps the rank). Their degrees are `q * r` and `(m - q) * r` (by `rfl`), and `terminal_degree_add_initial_degree` proves `(m - q) r + q r = m r`. |
| `Segment.splitShape Δ q hq hqm` | `BlockShape.ofPair` of `GL_(m r)` with sizes `((Δ.terminal q hqm).degree, (Δ.initial q hq).degree)`, i.e. `((m - q) r, q r)`. `splitShape_eq_ofPair` proves that it is literally the shape `ofPair (n - q r) (q r)` used in the vanishing clause, so both clauses concern the same family of splits `(n - l, l)`. |
| `Segment.splitFactors Δ q hq hqm π₁ π₂` | The dependent family `Fin.cons π₁ (Fin.cons π₂ finZeroElim)` of block factors of `splitShape`: block `0` carries `π₁` and block `1` carries `π₂`. Both evaluations hold by `rfl`. |

The sizes of `splitShape` are definitionally the degrees of the two subsegments.
This makes `π₁` and `π₂`, which live on the groups required by `IsSegmentHead`,
directly the block factors without any cast.

## Source correspondence and notation

The source, 3.4 (printed pp.181–182, PDF 18–19), whose hypotheses 9.5 adopts, takes
`ρ ∈ Irr G_m` cuspidal and `ρ' = ν^(k-1) ρ`, so `n = k m`.

- The source's `m` is the cuspidal rank, our `r = Δ.rank`.
- The source's `k` is the number of elements of the segment, our `m = Δ.length`.
  Section 3.1 instead writes `ρ' = ν^k ρ` with `k ≥ 0`; we follow the convention
  of 3.4.
- The source's `p` in `l = m p` is our `q`, so `l = q r`.
- The source's `⟨Δ⟩^t` is our `π`, and `⟨[ν^p ρ, ρ']⟩^t` and `⟨[ρ, ν^(p-1) ρ]⟩^t`
  are our `π₁` and `π₂`.
- The source's `r_{(n-l,l),(n)}` is our
  `T.normalizedJacquetFunctor (BlockShape.ofPair (n - l) l …)`.

9.5 states that `r_{(n-l,l),(n)}(⟨Δ⟩^t) = 0` if `m ∤ l`, and that
`r_{(n-l,l),(n)}(⟨Δ⟩^t) = ⟨[ν^p ρ, ρ']⟩^t ⊗ ⟨[ρ, ν^(p-1) ρ]⟩^t` if `l = m p`.
Its proof refers to the proof of 3.4. No erratum to Zelevinsky 1980 was found among
the registered literature or the Library notes.

**Factor order.** The first block, of size `n - l = (m - q) r`, carries the head of
the terminal segment. The second block, of size `l = q r`, carries the head of the
initial segment. This is the left-to-right order of the tensor product in 9.5. By
contrast, 3.4 for `⟨Δ⟩` uses the split `(l, n - l)` and puts the initial segment
first. That is a different representation and a different formula, which is not
stated here.

**Jacquet normalization.** Section 1 of the source uses the normalized functors
`r_{β,α}` of Bernstein–Zelevinsky 1977 for the standard upper block-triangular
parabolic. The Library's `T.normalizedJacquetFunctor B` takes coinvariants under
the unipotent radical of the upper block parabolic of `B`. The Levi then acts by the
inverse half modulus times the action of the embedded block-diagonal matrix
(`normalizedJacquet_mk_eq_inv_halfModulus`, with factor `(T.leviHalfModulus B m)⁻¹`).
The two normalizations agree. As a consistency check, take `r = 1`, `m = 2`,
`ρ = ν^(-1/2)` and `q = 1`. Then `π` is the Steinberg representation of `GL_2`,
whose normalized Jacquet module along the Borel is `ν^(1/2) ⊗ ν^(-1/2) = δ_B^(1/2)`.
That character is exactly the right-hand side, the heads of the one-element segments
`[ν^(1/2)]` and `[ν^(-1/2)]` in this order.

**Increasing head versus decreasing socle.** `T.IsSegmentHead Δ π` says that
`π` is an irreducible quotient of the increasing induction
`T.segmentInduced A.obj m _ = i(ρ, νρ, …, ν^(m-1) ρ)` for an actual supercuspidal
representative `A` of `ρ`, and that every irreducible quotient map has the same
kernel. This is the source's characterization of `⟨Δ⟩^t` in 9.1 as "the unique
irreducible quotient of `ρ × νρ × … × ρ'`". Section 9.1 equivalently describes
`⟨Δ⟩^t` as the unique irreducible submodule of the decreasing product
`ρ' × ν^(-1) ρ' × … × ρ`. That decreasing-socle description is not used as a
hypothesis, and its equivalence with the head form is not asserted here.

The hypothesis must also not be confused with `IsSegmentSocle` or
`IsSegmentSubrepresentation` of the increasing induction. Those describe the
source's `⟨Δ⟩` of 3.1, the unique irreducible submodule of `ρ × νρ × … × ρ'`. The
hypothesis is also not essential square-integrability; no analytic assumption
occurs.

## Scope

- **Endpoints.** Only proper splits `0 < l < n` are stated. The source's sum
  `c(⟨Δ⟩^t) = ⟨0⟩ ⊗ ⟨Δ⟩^t + … + ⟨Δ⟩^t ⊗ ⟨0⟩` also contains the endpoint terms
  `l = 0` and `l = n`. Those are the trivial identity cases, with an empty segment
  and a block `GL_0`. They are outside this unit. `Segment` requires positive
  length and `BlockShape` requires positive block sizes, so no empty segment or
  zero-rank block appears.
- **Length one.** If `m = 1` then every proper `l` satisfies `0 < l < r`, so
  `r ∤ l`. The vanishing clause asserts that all proper Jacquet modules vanish, and
  the formula clause is vacuous because no `q` satisfies `0 < q < 1`.
- No derivative, top derivative, genericity or exponent-norm conclusion is part of
  this unit.

## Unproved formula

This file proves no part of `SegmentHeadJacquetFormula`. An exact independent
proof must establish the actual Jacquet vanishing and isomorphism. The route of
3.4 (printed pp.181–182), as transferred by 9.5, combines the following
ingredients:

- vanishing of the Jacquet module of the cuspidal induction `ρ × νρ × … × ρ'`
  along `(n - l, l)` unless `r ∣ l` (the proof cites Bernstein–Zelevinsky 1977,
  2.13(a), or 1.6);
- exactness and transitivity of Jacquet functors (1.1(a), (c));
- nonvanishing of the further Jacquet module down to `(r, …, r)` on every
  composition factor of the two-block Jacquet module, which the proof deduces from
  the cuspidal support of 1.10;
- the one-term full cuspidal Jacquet module `ρ' ⊗ ν^(-1) ρ' ⊗ … ⊗ ρ` of `⟨Δ⟩^t`
  (9.1(*)), which forces the two-block Jacquet module to be irreducible;
- the Jacquet module of an external tensor product (1.5(a));
- recognition of the shorter heads from their full cuspidal Jacquet modules
  (9.1(*) for the shorter segments).

Each of these is a separate obligation, and none is supplied or assumed here. Only the published
definitions are imported: `Segment`, `CuspidalDatum.twist` (through
`Segment.member`), `IsSegmentHead`, `normalizedJacquetFunctor`,
`FiniteTensor.externalFunctor` and `BlockShape`/`Levi`.
