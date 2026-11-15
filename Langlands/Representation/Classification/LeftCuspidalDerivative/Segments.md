# Segment heads and socles are left reduced

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Segments`.

This file proves the last clause (segments) of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`: for an
actual supercuspidal `A` of `GL_d(F)` representing the cuspidal datum `κ`,

* `leftReduced_of_isSegmentSocle`: a segment socle of `Δ` is left `A`-reduced unless
  `Δ.base = κ`;
* `leftReduced_of_isSegmentHead`: a segment head of `Δ` is left `A`-reduced unless
  `Δ.last = κ`.

The mathematical input is first adjointness for `A × σ` (module `Frobenius`) together with
the two-block Jacquet formulas for segment socles and heads already in the Library
(`segmentSocleJacquetFormula`, `segmentHeadJacquetFormula`, Zelevinsky 1980, Propositions 3.4
and 9.5). Write `r` for the rank of the segment's cuspidal datum and `m = Δ.length`, so
`n = m r`. The two formulas parameterize the split differently:

* Socle: along `(d, n - d)` the Jacquet module vanishes unless `r` divides `d`, and for
  `d = q r` with `0 < q < m` it is `π₁ ⊠ π₂` with `π₁` a socle of the initial subsegment
  `Δ.initial q` (length `q`, degree `q r`) and `π₂` a socle of `Δ.terminal q`.
* Head: the Library formula is stated along `((m - q) r, q r)` with `0 < q < m`. There the
  Jacquet module is `π₁ ⊠ π₂` with `π₁` a head of the terminal subsegment `Δ.terminal q`
  (which removes the first `q` terms, so it has length `m - q` and degree `(m - q) r`) and
  `π₂` a head of `Δ.initial q`. Along `(d, k)` it vanishes unless `r` divides
  `k = n - d`. Equivalently, if the first block is `d = q' r`, then the first factor is a head
  of `Δ.terminal (m - q')`. The implementation uses the first parameterization: it writes
  `k = q r` and derives `d = (m - q) r`.

## Auxiliary results

* `ofPair_parabolic_ne_top`, `subsingleton_jacquet_of_isSupercuspidal`: a two-block
  parabolic is proper, so a supercuspidal representation has zero Jacquet module along it
  (`CuspidalSupport.standardJacquetSupercuspidalityClause`).
* `not_subsingleton_of_iso`: an object isomorphic to a nontrivial one is nontrivial.
* `length_eq_one_of_isSegmentSocle_of_isSupercuspidal`,
  `length_eq_one_of_isSegmentHead_of_isSupercuspidal`: if a segment socle (head) of `Δ` is
  supercuspidal then `Δ` has length one. Proof: if the length is at least two, the Jacquet
  formula with `q = 1` gives a Jacquet module isomorphic to `π₁ ⊠ π₂` with both factors
  irreducible, hence nonzero, contradicting supercuspidality.
* `exists_equiv_castRank_of_isSegmentHead_length_one`: a head of a one-term segment is
  equivalent to the rank transport of a supercuspidal representative of the base (the head
  is an irreducible quotient of the one-term induced representation, which is the
  representative itself, `singletonSegmentInducedEquiv`). For socles the Library already
  has `SegmentSocleDerivativesProof.exists_equiv_castRank_of_length_one`.
* `last_eq_base_of_length_eq_one`: a one-term segment ends at its base.
* `isSegmentSocle_supercuspidal_target`, `isSegmentHead_supercuspidal_target`: a nonzero
  intertwiner from a segment socle (head) `π` of `Δ` to an irreducible supercuspidal `A'`
  is an equivalence (Schur), so `π` is supercuspidal, `Δ` has length one, and `A'` is
  equivalent to the rank transport of a representative of `Δ.base`.
* `cuspidalDatum_eq_of_castRank_equiv`: two cuspidal data whose supercuspidal
  representatives become equivalent after rank transport to a common rank are equal
  (`CuspidalSupport.cuspidalDatum_eq_of_equiv`).
* `nonempty_equiv_of_isSubquotient_irreducible`: an irreducible subquotient of an
  irreducible representation is equivalent to it.

## Proof of the main theorems (as implemented)

Socle case. Let `Z` be an irreducible subquotient of the socle `π` with
`Z ↪ A × σ`, `σ` on `GL_k`, `d + k = n`. Then `Z ≅ π`, so `Z` is again a segment socle of
`Δ`. We show `Δ.base = κ`.

* `k = 0`: Frobenius reciprocity gives a nonzero map `Z → A` (rank-transported); by the
  target lemma `Δ` has length one and `A` is equivalent to a representative of `Δ.base`,
  so `Δ.base = κ`.
* `k > 0`: Frobenius reciprocity gives a nonzero map from the Jacquet module of `Z` along
  `(d, k)` to `A ⊠ σ`. If `r ∤ d` that Jacquet module is zero, a contradiction. If
  `d = q r`, after substituting `d` and `k = (m - q) r` the two-block shapes agree
  definitionally, and composing with the Jacquet isomorphism gives a nonzero map
  `π₁ ⊠ π₂ → A ⊠ σ`, hence (module `Frobenius`, `exists_firstFactor_ne_zero`) a nonzero
  map `π₁ → A` with `π₁` a socle of `Δ.initial q`. The target lemma gives that
  `Δ.initial q` has length one and its base, which is `Δ.base`, is represented by a
  representation equivalent to `A`; hence `Δ.base = κ`.

Head case. Identical, with the head Jacquet formula: the divisibility condition is on `k`.
If `k = q r`, then `0 < q < m` and `d = (m - q) r`, and `π₁` is a head of `Δ.terminal q`
(length `m - q`, degree `d`); the target lemma makes `Δ.terminal q` a one-term segment,
and `(Δ.terminal q).base = (Δ.terminal q).last = Δ.last` (`Segment.terminal_last`), so
`Δ.last = κ`.
