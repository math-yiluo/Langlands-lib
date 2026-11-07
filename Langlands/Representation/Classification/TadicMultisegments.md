# Tadić's multisegments `a(n,d)^ρ`, the block set `X_k` and the statement `(U^m)`

Author: Worker 1792. This pair adds definitions and Prop-valued relations
only. It proves bookkeeping lemmas (number of segments, degree, the rank of a
Zelevinsky socle of `a(n,d)^ρ`, positivity of the rank of members of `X_k`,
emptiness of `X_0`) and one definitional equality. It asserts no existence,
irreducibility or unitarizability, and it adds no axiom or structure field.

Source: M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci.
ÉNS (4) 19 (1986), literature ID `tadic-1986-unitary`: §3.1 (printed p. 352),
§4.6 (printed p. 358) and Lemma 4.8 (printed p. 360, PDF page 27); for the
Hermitian contragredient, §2.1-§2.3 (printed p. 345) and §4.2-§4.4
(printed pp. 357-358). Tadić's `ℕ` is the set of positive integers
(printed p. 339).

All declarations lie in `Langlands.Classification`, with implicit `p`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`, and with the field and
representation universes `uF`, `uV` independent. Segments, multisegments,
cuspidal data and their twists are the published ones from
`Classification.Segments`. A segment with base `ρ` and length `l` is
`[ρ, νρ, …, ν^(l-1)ρ]`, where `ν = |det|_F` and twisting by `ν^s` is
`CuspidalDatum.twist s`.

## Centered segments and `a(n,d)^ρ`

`tadicCenteredSegment ρ d hd x` is the segment of length `d > 0` with base
`ρ.twist (x - (d-1)/2)`, computed in `ℝ`. It is
`ν^x Δ[d]^ρ = [ν^(x-(d-1)/2) ρ, ν^(x+(d-1)/2) ρ]`, where Tadić's §3.1 segment
is `Δ[d]^ρ = [ν^(-(d-1)/2) ρ, ν^((d-1)/2) ρ]`. Its length is `d` and its
rank is the rank of `ρ`; the two simp lemmas `tadicCenteredSegment_length`
and `tadicCenteredSegment_rank` record this by `rfl`.

`tadicMultisegment ρ n d hd` is the multiset image of `Multiset.range n` under
`j ↦ tadicCenteredSegment ρ d hd (j - (n-1)/2)`, again with real
subtraction. It consists of the `n` segments
`ν^(-(n-1)/2) Δ[d]^ρ, ν^(-(n-1)/2+1) Δ[d]^ρ, …, ν^((n-1)/2) Δ[d]^ρ`, which is
Tadić's `a(n,d)^ρ` of §4.6 (notation of §3.1). Thus `a(1,d)^ρ = Δ[d]^ρ` and
`a(n,1)^ρ` consists of `n` one-point segments. Tadić takes `n, d ∈ ℕ`
positive. The construction requires `d > 0` (segments have positive length)
but, as a raw helper, also accepts `n = 0`, where it gives the empty
multisegment; that case is outside Tadić's notation, and the predicates
`IsTadicXBlock` and `TadicSocleUnitarity` below require `0 < n` explicitly.

Proved facts:

- `tadicMultisegment_card`: the multisegment has exactly `n` segments.
- `tadicMultisegment_degree`: its published degree, the sum of
  `length * rank` over the segments, is `n * (d * ρ.rank)`. So any
  representation attached to it lives on `GL_(n d deg ρ)`.
- `tadicMultisegment_rank_eq_of_isZelevinskySocle`: if `σ` on `GL_N` is a
  Zelevinsky socle of `tadicMultisegment ρ n d hd`, then
  `N = n * (d * ρ.rank)`. The proof reads off the degree sum of the
  witnessing segment-product datum and applies `tadicMultisegment_degree`.

## The complementary product `ν^α σ × ν^(-α) σ`

`tadicComplementaryProduct hM σ α`, for an actual smooth complex
representation `σ` of `GL_M(F)` with `M > 0` and `α : ℝ`, is
`T.twistedProductInduced` of the uniform block shape
`BlockShape.uniform 2 M hM`, the constant family `σ`, and exponent `α` on the
first block and `-α` on the second. So it is the same-representation product
`ν^α σ × ν^(-α) σ` for arbitrary `σ`, built from the published normalized
upper-block parabolic induction and real-power twist. No irreducibility is
assumed.

Relation to Tadić's `π(σ, α)`. In general Tadić's product is
`π(σ, α) = ν^α σ × ν^(-α) σ^+`, with `σ^+` the Hermitian contragredient
(§2.1; §4.2 and §4.4, printed pp. 357-358). It agrees with
`tadicComplementaryProduct hM σ α` when `σ` is Hermitian (`σ^+ ≅ σ`), and
this is the only case used for `X_k`: there `σ = ⟨a(n,d)^ρ⟩` with `ρ`
unitary. By §2.2, `⟨a⟩^+ = ⟨a^+⟩`, and by §2.3, for unitary `ρ` the operation `+`
sends `ν^x ρ` to `ν^(-x) ρ`. It therefore maps each centered segment
`ν^c Δ[d]^ρ` to `ν^(-c) Δ[d]^ρ`, and since the set of centers
`{j - (n-1)/2 : 0 ≤ j < n}` is symmetric under `c ↦ -c`, `a(n,d)^ρ` is
fixed by `+`. So `⟨a(n,d)^ρ⟩` is Hermitian. This module neither uses nor
proves the Hermitian property; the remark only explains the source
correspondence. The target `TadicUnitaryDualExhaustion` uses the
same-representation product (`SpehDatum.complementaryInduced`).

`SpehDatum.complementaryInduced_eq_tadicComplementaryProduct` proves, by
`rfl`, that the published `SpehDatum.complementaryInduced S α` of
`Classification.TadicUnitaryStatement` is this product for `M = d.degree`.

## Tadić's set `X_k`

`IsTadicXBlock k τ`, for a representation `τ` of `GL_N(F)`, holds exactly when
one of the following holds.

1. There are a unitary cuspidal datum `ρ` (`ρ.IsUnitary`: its supercuspidal
   class is unitarizable, from `Supercuspidal.UnitarySupport`), natural
   numbers `n > 0` and `d > 0`, with `N ≤ k`, such that
   `(tadicMultisegment ρ n d hd).IsZelevinskySocle τ`.
2. There are such `ρ, n > 0, d > 0`, a positive `M ≤ k`, a representation `σ` of
   `GL_M(F)` with `(tadicMultisegment ρ n d hd).IsZelevinskySocle σ`, a real
   `α` with `0 < α < 1/2`, and an equality `2 * M = N`, such that `τ` is
   isomorphic to the transport along that equality of
   `tadicComplementaryProduct hM σ α`.

Here `IsZelevinskySocle` is the published relation
`Multisegment.IsZelevinskySocle` of `Classification.LanglandsData`: for some
precedence-ordered ordering of the multisegment and socles of its segments,
the representation is the irreducible socle of the corresponding normalized
product. It is Zelevinsky's `⟨a⟩`; independence of the ordering is not
asserted by the relation.

With `k = m - 1` this is Tadić's set
`X_(m-1) = {⟨a(n,d)^ρ⟩, π(⟨a(n,d)^ρ⟩, α) : n, d ∈ ℕ, ρ ∈ C^u,
(nd) deg ρ ≤ m-1, 0 < α < 1/2}` of §4.6 and Lemma 4.8, with `n, d`
positive as in Tadić, and with `π(σ, α)` in its Hermitian form explained
above. The bound
`(nd) deg ρ ≤ m-1` appears as `N ≤ k` in the first case and as `M ≤ k` in
the second, since by `tadicMultisegment_degree` a Zelevinsky socle of
`a(n,d)^ρ` on `GL_N` has `N = n d deg ρ`. Case 2 places no bound on `N = 2M`
itself, matching Tadić, whose bound concerns `⟨a(n,d)^ρ⟩`.

Proved facts:

- `IsTadicXBlock.rank_pos`: a member of `X_k` on `GL_N` has `N > 0`. In
  case 1, `N = n * (d * ρ.rank)` with all three factors positive; in case 2,
  `N = 2 * M` with `M > 0`.
- `not_isTadicXBlock_zero`: `X_0` is empty, as in Tadić (all degrees are
  positive). Indeed `N ≤ 0` in case 1 and `M ≤ 0` in case 2 contradict
  positivity.

## The statement `(U^m)`

`TadicSocleUnitarity F T m` is the Prop asserting: for every cuspidal datum
`ρ` with `ρ.IsUnitary`, all `n > 0` and `d > 0`, and every representation `σ`
of `GL_N(F)` with `N ≤ m` that is a Zelevinsky socle of
`tadicMultisegment ρ n d hd`, `σ` is unitarizable (`IsUnitarizable`: it
carries an actual invariant positive definite Hermitian form). This is
Tadić's `(U^m)` of §4.6: "if `n, d ∈ ℕ` and `ρ ∈ C^u` such that
`(nd) deg ρ ≤ m` then `⟨a(n,d)^ρ⟩` is unitarizable." It is a hypothesis
family indexed by `m`, used in Lemma 4.8 and in the induction of the
appendix; it is not asserted here. The cuspidal data and representations
use the representation universe `max uF uV` of the target interface.
