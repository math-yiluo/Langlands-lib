# Genericity of `A × μ_z` for all but finitely many `z`

Module `Langlands.Representation.RankinSelberg.HighlyRamified.PairInductionGenericity`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It proves
`PairInductionGenericity`, the genericity input of the rank reduction in
`HighlyRamified.RankReduction`. Let `A` be a smooth representation of
`GL_(n+1)(F)` that is generic for `ψ`, and let `μ_z` be the unramified
character `x ↦ z ^ ord(x)` of `GL_1(F)` (`unramifiedRankOne F z`). Then the
normalized induced representation `A × μ_z = pairInduced F A μ_z` of
`GL_(n+2)(F)` is generic for `ψ` for all `z : ℂˣ` outside a finite set.
"Generic" is the Library's `Whittaker.IsGeneric`, which includes irreducibility
and admissibility.

## Provenance

Jacquet and Shalika 1985, §4.3 (printed page 327) do not need this statement.
They replace a representation by the generic constituent of the induced
representation. The Library's gamma multiplicativity is stated for generic
induced representations, so the Lean reduction instead chooses `z` with
`A × μ_z` itself generic. This is a standard consequence of Zelevinsky's
classification of generic representations (Zelevinsky 1980, Theorem 9.7, p.199,
and §9.10, p.201). In the Library this classification is
`Classification.GenericSegmentProductExhaustion`, proved as
`Classification.genericSegmentProductExhaustion`. It says that a smooth
representation is generic if and only if it is isomorphic to the product of
special heads over an unlinked multisegment. The derivation below is internal
to this project. The source does not state it as a separate lemma.

## Definitions

All definitions use the canonical topological data
`F.canonicalTopologicalData` of the p-adic field `F`.

- `unramifiedSupercuspidal F z`: `μ_z` as a supercuspidal representation of
  `GL_1(F)`. It is irreducible because it is one-dimensional, and
  supercuspidal by `isSupercuspidal_rankOne`.
- `unramifiedCuspidalDatum F z`: the cuspidal datum `[μ_z]` of rank one, the
  isomorphism class of `unramifiedSupercuspidal F z`.
- `unramifiedSingletonDatum F z`: the segment-product datum of rank one with
  one segment, the one-term segment `{[μ_z]}` (`singletonSegment`), and block
  `μ_z` cast to the degree of that segment.
- `pairDatum F d s`: the family of two inner data `(d, s)` over the block shape
  `(n + 1, 1)` (`succBlockShape (pairSizes n) _`), for data `d` of rank `n + 1`
  and `s` of rank one.
- `equivOfEq`: moves an equivalence `ρ ≃ Y` of smooth representations along
  equalities `π = ρ` and `X = Y` of smooth representations, by substitution.
- `pairBlockEquiv A B d s eA eB`: the two equivalences `eA : A ≃ i(d)` and
  `eB : B ≃ i(s)` as a family over the two blocks of `(n + 1, 1)`. Here `i(d)`
  is the product `d.induced` of a datum.
- `pairConcatenateEquiv A B d s eA eB`: an equivalence from `A × B` to the
  product of the concatenation `SegmentProductDatum.concatenate` of `(d, s)`.
  It is `normalizedProductInducedEquiv` applied to `pairBlockEquiv`, followed by
  `concatenateInducedEquiv`, which regroups the outer product of the inner
  products into one flat product.

## Lemmas

- `blockShape_one_length`: a block shape of rank one has one block.
- `isSupercuspidal_rankOne`: an admissible representation of `GL_1` is
  supercuspidal. Every block parabolic of `GL_1` is the whole group
  (`singleBlock_parabolic_eq_top`), so there is no proper parabolic.
- `isAdmissible_unramifiedRankOne`: `μ_z` is admissible, from
  `rankOneExtensionCharacter_isOfWhittakerType`.
- `unramifiedCuspidalDatum_injective`: `z ↦ [μ_z]` is injective. An
  isomorphism `μ_z ≅ μ_w` carries the scalar character of `μ_w` to that of
  `μ_z`. At the scalar matrix of a uniformizer `ϖ` the two characters take the
  values `μ_w(ϖ) = w` and `μ_z(ϖ) = z`.
- `twist_natCast_injective`: if `ν^a β = ν^b β` for natural `a, b`, then
  `a = b`. This is `cuspidalIntegralTwistFreeness` applied to `ν^(a-b)`.
- `mem_support_singletonSegment`: the support of `{ρ}` is `{ρ}`.
- `exists_twist_of_singletonSegment_isLinked`: if `{ρ}` is linked with a
  segment `Δ`, then `ρ = ν^k b(Δ)` for an integer `k` with
  `-1 ≤ k ≤ length Δ`, where `b(Δ)` is the base of `Δ`. Proof: linkage says that
  `ρ ∉ Δ` and that the union of the supports of `{ρ}` and `Δ` is the support of
  a segment `Δ'`. Let `b(Δ) = ν^(i₀) b(Δ')` and `ρ = ν^(j₀) b(Δ')`. Every other
  member of `Δ'` lies in `Δ`, so its index is in `[i₀, i₀ + length Δ)`, by
  `twist_natCast_injective`. If `i₀ > j₀ + 1`, the index `i₀ - 1` is neither
  `j₀` nor in that range. If `j₀ > i₀ + length Δ`, the index `i₀ + length Δ`
  is neither. So `k = j₀ - i₀` lies in `[-1, length Δ]`.
- `singletonSegment_isSegmentHead`: for a supercuspidal representative `A` of
  `ρ`, the block `A` cast to the degree of `{ρ}` is a segment head of `{ρ}`. The
  product over the one-term segment is `A` itself
  (`singletonSegmentInducedEquiv`), and an irreducible representation is its own
  irreducible head.
- `unramifiedSingletonDatum_hasSegmentHeads`: the block of `{[μ_z]}` is a
  segment head.
- `unramifiedSingletonDatumEquiv`: an equivalence from `μ_z` to the product of
  `{[μ_z]}`. It combines `rankOneExtensionCharacterUniverseEquiv` (the
  universe change of `μ_z`) and `SegmentProductOrderedAssembly.singletonIso`.
- `mem_unramifiedSingletonDatum_multisegment`: every segment of `{[μ_z]}` is
  `{[μ_z]}`.
- `pairDatum_hasSegmentHeads`, `mem_pairDatum_multisegment`: both inner data
  of `(d, s)` are products of segment heads when `d` and `s` are, and each
  segment of an inner datum is a segment of `d` or of `s`.
- `concatenate_hasSegmentHeads`, `mem_concatenate_multisegment`: a
  concatenation of products of segment heads is a product of segment heads, and
  each of its segments is a segment of an inner datum.
- `isGeneric_pairInduced_of_concatenate`: if the product of the concatenation
  of `(d, s)` is generic, then so is `A × B`, through `pairConcatenateEquiv` and
  `Whittaker.isGeneric_iff_of_equiv`.
- `isGeneric_pairInduced_of_datum`: let `A ≃ i(d)` and `B ≃ i(s)`. Suppose `d`
  and `s` are products of segment heads, the multisegment of `d` is unlinked,
  every segment of `s` equals one segment `Δ`, and `Δ` is linked with no
  segment of `d`. Then `A × B` is generic. Each segment of the concatenation is
  a segment of `d` or equals `Δ`. So the concatenation is unlinked: `Δ` is not
  linked with itself, since linkage requires that neither support contains the
  other. The backward direction of `genericSegmentProductExhaustion` makes its
  product generic, and `isGeneric_pairInduced_of_concatenate` concludes.

All these lemmas keep `B` and `s` abstract. The concrete data `μ_z` and
`{[μ_z]}` are supplied only in `pairInductionGenericity`.

## Main theorems

- `pairInductionGenericity : PairInductionGenericity.{uF, uX}`. Proof: let `A`
  be generic of rank `n + 1` with space in universe `uX`. Its universe lift to
  `max uF uX` (`SmoothRep.universeLift`) is generic. The forward direction of
  `genericSegmentProductExhaustion` gives a datum `d` of segment heads over an
  unlinked multisegment and an isomorphism of the lift with `i(d)`. Let `S` be
  the set of `z` with `[μ_z] = ν^k b(Δ_i)` for a segment `Δ_i` of `d` and an
  integer `-1 ≤ k ≤ length Δ_i`. It is a finite union over `i` and `k`, and each
  piece has at most one element by `unramifiedCuspidalDatum_injective`. So `S`
  is finite. For `z ∉ S`, apply `isGeneric_pairInduced_of_datum` with `B = μ_z`,
  `s = {[μ_z]}` and `Δ = {[μ_z]}`. If `{[μ_z]}` were linked with a segment of
  `d`, then `exists_twist_of_singletonSegment_isLinked` would put `z` in `S`.
  Hence every `z` with `A × μ_z` not generic lies in `S`.
- `highlyRamifiedGammaStability_of_adjacent_and_rankOne`: let the adjacent case
  `∀ n, PairStability (n + 1) n` hold at universes `(uV, uW)`,
  `(max uF uV, uW)` and `(uV, max uF uW)`, and the rank-one case
  `∀ r, PairStability r 0` hold at `(uV, uW)` and `(uV, max uF uW)`. Then
  `HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` holds. This is
  `highlyRamifiedGammaStability_of_adjacent_of_rankOne` from
  `HighlyRamified.RankReduction`. Its four genericity hypotheses are supplied by
  `pairInductionGenericity` at `uV`, `max uF uV`, `uW` and `max uF uW`. This
  module does not prove the adjacent and rank-one cases.
